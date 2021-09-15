/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#include<math.h>
#include "util/luby.h"
#include "util/warning.h"
#include "util/timeit.h"
#include "util/union_find.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_translation.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/proofs/proof_checker.h"
#include "ast/ast_util.h"
#include "ast/well_sorted.h"
#include "model/model.h"
#include "model/model_pp.h"
#include "smt/smt_context.h"
#include "smt/smt_quick_checker.h"
#include "smt/uses_theory.h"
#include "smt/smt_for_each_relevant_expr.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_model_finder.h"
#include "smt/smt_parallel.h"
#include "smt/smt_arith_value.h"
#define NIDL_DEBUG

namespace smt {

    context::context(ast_manager & m, smt_params & p, params_ref const & _p):
        m(m),
        m_fparams(p),
        m_params(_p),
        m_setup(*this, p),
        m_relevancy_lvl(m_fparams.m_relevancy_lvl),
        m_asserted_formulas(m, p, _p),
        m_rewriter(m),
        m_qmanager(alloc(quantifier_manager, *this, p, _p)),
        m_model_generator(alloc(model_generator, m)),
        m_relevancy_propagator(mk_relevancy_propagator(*this)),
        m_user_propagator(nullptr),
        m_random(p.m_random_seed),
        m_flushing(false),
        m_lemma_id(0),
        m_progress_callback(nullptr),
        m_next_progress_sample(0),
        m_clause_proof(*this),
        m_fingerprints(m, m_region),
        m_b_internalized_stack(m),
        m_e_internalized_stack(m),
        m_l_internalized_stack(m),
        m_final_check_idx(0),
        m_is_auxiliary(false),
        m_par(nullptr),
        m_par_index(0),
        m_cg_table(m),
        m_is_diseq_tmp(nullptr),
        m_units_to_reassert(m),
        m_qhead(0),
        m_simp_qhead(0),
        m_simp_counter(0),
        m_bvar_inc(1.0),
        m_phase_cache_on(true),
        m_phase_counter(0),
        m_phase_default(false),
        m_conflict(null_b_justification),
        m_not_l(null_literal),
        m_conflict_resolution(mk_conflict_resolution(m, *this, m_dyn_ack_manager, p, m_assigned_literals, m_watches)),
        m_unsat_proof(m),
        m_dyn_ack_manager(*this, p),
        m_unknown("unknown"),
        m_unsat_core(m),
#ifdef Z3DEBUG
        m_trail_enabled(true),
#endif
        m_scope_lvl(0),
        m_base_lvl(0),
        m_search_lvl(0),
        m_generation(0),
        m_last_search_result(l_undef),
        m_last_search_failure(UNKNOWN),
        m_searching(false) {
        m_ls_solver=new boolidl::bool_ls_solver();
        SASSERT(m_scope_lvl == 0);
        SASSERT(m_base_lvl == 0);
        SASSERT(m_search_lvl == 0);

        m_case_split_queue = mk_case_split_queue(*this, p);
        m_rewriter.updt_params(m_asserted_formulas.get_params());

        init();

        if (!relevancy())
            m_fparams.m_relevancy_lemma = false;

        m_model_generator->set_context(this);
    }


    /**
       \brief retrieve flag for when cancelation is possible.
       获得 可以取消时 的检索标志，每次都会对m_counter加一，如果超过阈值就会cancel
    */

    bool context::get_cancel_flag() {
        return !m.limit().inc();
    }
    //更新参数，在context生成函数中被调用
    void context::updt_params(params_ref const& p) {
        m_params.append(p);
        m_asserted_formulas.updt_params(p);
        if (!m_setup.already_configured()) {
            m_fparams.updt_params(p);
        }
    }
    //返回m_relevancy_lvl和参数中m_relevancy_lvl的最小值
    unsigned context::relevancy_lvl() const {
        return std::min(m_relevancy_lvl, m_fparams.m_relevancy_lvl);
    }
    //拷贝一个context从源ctx到目标ctx，无调用
    void context::copy(context& src_ctx, context& dst_ctx, bool override_base) {
        ast_manager& dst_m = dst_ctx.get_manager();
        ast_manager& src_m = src_ctx.get_manager();
        src_ctx.pop_to_base_lvl();

        if (!override_base && src_ctx.m_base_lvl > 0) {
            throw default_exception("Cloning contexts within a user-scope is not allowed");
        }
        SASSERT(src_ctx.m_base_lvl == 0 || override_base);

        ast_translation tr(src_m, dst_m, false);

        dst_ctx.set_logic(src_ctx.m_setup.get_logic());
        dst_ctx.copy_plugins(src_ctx, dst_ctx);

        asserted_formulas& src_af = src_ctx.m_asserted_formulas;
        asserted_formulas& dst_af = dst_ctx.m_asserted_formulas;

        // Copy asserted formulas.
        for (unsigned i = 0; i < src_af.get_num_formulas(); ++i) {
            expr_ref fml(dst_m);
            proof_ref pr(dst_m);
            proof* pr_src = src_af.get_formula_proof(i);
            fml = tr(src_af.get_formula(i));
            if (pr_src) {
                pr = tr(pr_src);
            }
            dst_af.assert_expr(fml, pr);
        }

        src_af.get_macro_manager().copy_to(dst_af.get_macro_manager());

        if (!src_ctx.m_setup.already_configured()) {
            return;
        }

        for (unsigned i = 0; !src_m.proofs_enabled() && i < src_ctx.m_assigned_literals.size(); ++i) {
            literal lit = src_ctx.m_assigned_literals[i];
            bool_var_data const & d = src_ctx.get_bdata(lit.var());
            if (d.is_theory_atom() && !src_ctx.m_theories.get_plugin(d.get_theory())->is_safe_to_copy(lit.var())) {
                continue;
            }
            expr_ref fml0(src_m), fml1(dst_m);
            src_ctx.literal2expr(lit, fml0);
            fml1 = tr(fml0.get());
            dst_ctx.assert_expr(fml1);
        }

        dst_ctx.setup_context(dst_ctx.m_fparams.m_auto_config);
        dst_ctx.internalize_assertions();
        
        dst_ctx.copy_user_propagator(src_ctx);

        TRACE("smt_context",
              src_ctx.display(tout);
              dst_ctx.display(tout););
    }
    //context的析构函数，释放被context占用的资源
    context::~context() {
        flush();
        m_asserted_formulas.finalize();
    }
    //将src中的m_theory_set中的理论注册进新dst context中， 该方法在copy，mk_fresh中调用
    void context::copy_plugins(context& src, context& dst) {
        // copy theory plugins
        for (theory* old_th : src.m_theory_set) {
            theory * new_th = old_th->mk_fresh(&dst);
            if (!new_th)
                throw default_exception("theory cannot be copied");
            dst.register_plugin(new_th);
        }
    }
    //在copy中调用
    void context::copy_user_propagator(context& src_ctx) {
        if (!src_ctx.m_user_propagator) 
            return;
        ast_translation tr(src_ctx.m, m, false);
        auto* p = get_theory(m.mk_family_id("user_propagator"));
        m_user_propagator = reinterpret_cast<user_propagator*>(p);
        SASSERT(m_user_propagator);
        for (unsigned i = 0; i < src_ctx.m_user_propagator->get_num_vars(); ++i) {
            app* e = src_ctx.m_user_propagator->get_expr(i);
            m_user_propagator->add_expr(tr(e));
        }
    }
    //无调用，调用mk_fresh
    context * context::mk_fresh(symbol const * l, smt_params * p, params_ref const& pa) {
        context * new_ctx = alloc(context, m, p ? *p : m_fparams, pa);
        new_ctx->m_is_auxiliary = true;
        new_ctx->set_logic(l == nullptr ? m_setup.get_logic() : *l);
        copy_plugins(*this, *new_ctx);
        return new_ctx;
    }
    //初始化操作!!!
    void context::init() {
        app * t       = m.mk_true();
        mk_bool_var(t);//首先构造一个为真的bool变量t
        SASSERT(get_bool_var(t) == true_bool_var);
        SASSERT(true_literal.var() == true_bool_var);
        m_assignment[true_literal.index()]     = l_true;//真假文字赋值为相应的值
        m_assignment[false_literal.index()]    = l_false;
        if (m.proofs_enabled()) {//如果使用证明
            proof * pr = m.mk_true_proof();

            set_justification(true_bool_var, m_bdata[true_bool_var], b_justification(mk_justification(justification_proof_wrapper(*this, pr))));//为真文字设置验证
        }
        else {
            m_bdata[true_bool_var].set_axiom();//如果不使用,直接给真文字设置原子作为证明
        }
        m_true_enode  = mk_enode(t, true, true, false);
        // internalizer is marking enodes as interpreted whenever the associated ast is a value and a constant.
        // m_true_enode->mark_as_interpreted();
        //每当关联的ast是一个值和一个常数时，内化器就将enode标记为解释的。
        app * f       = m.mk_false();
        m_false_enode = mk_enode(f, true, true, false);
        // m_false_enode->mark_as_interpreted();
    }
    //设置回调函数
    void context::set_progress_callback(progress_callback *cb) {
        m_progress_callback = cb;
    }

    /**
       \brief This method should be used to create equality atoms during the search.
       See comments in theory::mk_eq_atom
       该方法应该在搜索过程中被用来构造等式原子
       在assume_eq中被调用
    */
    app * context::mk_eq_atom(expr * lhs, expr * rhs) {
        family_id fid = m.get_sort(lhs)->get_family_id();
        theory * th   = get_theory(fid);
        if (th)//如果lhs的family_id对应的理论存在，则用该理论构造等式原子并返回
            return th->mk_eq_atom(lhs, rhs);
        if (lhs->get_id() > rhs->get_id())
            std::swap(lhs, rhs);//保证lhs的id比rhs的id小
        return m.mk_eq(lhs, rhs);//如果该理论不存在，就调用ast_manager的mk_eq构造等式原子
    }
    //设置验证，justification，为data d设置相应的justification
    void context::set_justification(bool_var v, bool_var_data& d, b_justification const& j) {
        SASSERT(validate_justification(v, d, j));
        d.set_justification(j);
    }

    //将l对应的bool变量赋值为l的取值，改变m_assignment中的赋值，将l对应的变量数据的phase设置为相反取值，decision表示是否为一次决策操作，在BCP中被调用
    void context::assign_core(literal l, b_justification j, bool decision) {
        m_assigned_literals.push_back(l);//赋值的文字入栈
        m_assignment[l.index()]    = l_true;//将文字所在位置设为true
        m_assignment[(~l).index()] = l_false;//文字的非的位置设为false
        bool_var_data & d          = get_bdata(l.var());//d是l对应的bool变量数据
        set_justification(l.var(), d, j);
        d.m_scope_lvl              = m_scope_lvl;
        if (m_fparams.m_restart_adaptive && d.m_phase_available) {
            m_agility             *= m_fparams.m_agility_factor;//略微减小agility
            if (!decision && d.m_phase == l.sign())
                m_agility         += (1.0 - m_fparams.m_agility_factor);//如果decision是false，表示不是一次decision操作，并且phase与l的赋值相同，就需要增大agility，也就是敏捷性，以备重启使用
        }
        d.m_phase_available        = true;
        d.m_phase                  = !l.sign();//将l对应的bool变量的phase设置层l的相反符号
        TRACE("assign_core", tout << (decision?"decision: ":"propagating: ") << l << " ";
              display_literal_smt2(tout, l) << "\n";
              tout << "relevant: " << is_relevant_core(l) << " level: " << m_scope_lvl << " is atom " << d.is_atom() << "\n";
              /*display(tout, j);*/
              );
        TRACE("phase_selection", tout << "saving phase, is_pos: " << d.m_phase << " l: " << l << "\n";);

        if (d.is_atom() && (relevancy_lvl() == 0 || (relevancy_lvl() == 1 && !d.is_quantifier()) || is_relevant_core(l))) {
            m_atom_propagation_queue.push_back(l);
        }

        if (m.has_trace_stream())
            trace_assign(l, j, decision);

        m_case_split_queue->assign_lit_eh(l);
    }
    //进行bool约束传播，如果发生冲突则返回false，否则成功传播返回true!!!
    bool context::bcp() {
        SASSERT(!inconsistent());
        while (m_qhead < m_assigned_literals.size()) {//该操作会改变m_head
            if (get_cancel_flag()) {
                return true;
            }
            literal l      = m_assigned_literals[m_qhead];//m_qhead指向还未处理的已赋值变量
            SASSERT(get_assignment(l) == l_true);
            m_qhead++;
            m_simp_counter--;
            literal not_l  = ~l;//该文字的非
            SASSERT(get_assignment(not_l) == l_false);//该文字的非应该为false，因为该文字是被assigned，必然为真
            watch_list & w = m_watches[l.index()];//w是l watch的子句/文字 列表，对应的是l的非所在的子句（其原本非false，现在变为false），not_l 在该子句中
            if (binary_clause_opt_enabled()) {//如果使用二元子句优化，进行二元子句传播
                // binary clause propagation
                b_justification js(l);
                literal * it  = w.begin_literals();
                literal * end = w.end_literals();
                for(; it != end; ++it) {//逐个遍历被l watch的二元子句中的文字l
                    literal l = *it;
                    switch (get_assignment(l)) {
                    case l_false://如果当前l是false，则报告冲突
                        m_stats.m_num_bin_propagations++;
                        set_conflict(js, ~l);
                        return false;
                    case l_undef://如果l未定义，则直接赋值
                        m_stats.m_num_bin_propagations++;
                        assign_core(l, js);
                        break;
                    case l_true://如果l已经未true，则跳过
                        break;
                    }
                }
            }

            // non-binary clause propagation 非二元子句传播
            watch_list::clause_iterator it  = w.begin_clause();
            watch_list::clause_iterator it2 = it;//it2指向l watch的最后一个子句
            watch_list::clause_iterator end = w.end_clause();
            for(; it != end; ++it) {//用it遍历w中的每个被watch的子句
                clause * cls = *it;
                CTRACE("bcp_bug", cls->get_literal(0) != not_l && cls->get_literal(1) != not_l, display_clause_detail(tout, cls);
                       tout << "not_l: "; display_literal(tout, not_l); tout << " " << not_l << "\n";);
                SASSERT(cls->get_literal(0) == not_l || cls->get_literal(1) == not_l);
                if (cls->get_literal(0) == not_l) {
                    cls->set_literal(0, cls->get_literal(1));
                    cls->set_literal(1, not_l);
                }//要把被watch的子句的第2号设为not l，因为此时它已经是false了

                SASSERT(cls->get_literal(1) == not_l);//l watch的子句的第2个文字是l的非

                literal first_lit     = cls->get_literal(0);
                lbool   first_lit_val = get_assignment(first_lit);

                if (first_lit_val == l_true) {//另一个watch是true
                    *it2 = *it; // clause is already satisfied, keep it 如果该子句已经被满足了，则保留它，因为在该子句中只有first_lit这一个真文字
                    it2++;
                }
                else {//如果第一个文字不是true，表示它是undef或者false
                    literal * it3  = cls->begin() + 2;//it3表示从子句cls的第三位开始的文字
                    literal * end3 = cls->end();
                    for(; it3 != end3; ++it3) {
                        if (get_assignment(*it3) != l_false) {//遍历子句cls中的文字，如果对应的不是false
                            // swap literal *it3 with literal at position 0
                            // the negation of literal *it3 will watch clause cls.如果it3对应的的赋值不是false，也就找到了cls的watch子句，将it3和位置0的文字交换，用it3的非来watch该子句
                            m_watches[(~(*it3)).index()].insert_clause(cls);
                            cls->set_literal(1, *it3);
                            *it3   = not_l;//将it3文字和1号位置的文字交换，it3号的位置是个可以作为watch的
                            goto found_watch;
                        }
                    }
                    // did not find watch...如果没有找到watch文字，即不是false的文字，则存在2种情况，另一个watch已经为false，则冲突，另一个watch是undef则单元传播
                    if (first_lit_val == l_false) {//如果第一个文字是false，则说明该子句中所有文字都是false，说明该子句是假的
                        // CONFLICT 产生冲突，所有文字都是假的，该子句为冲突
                        // copy remaining watches 将watch 列表中的逐个向前复制，覆盖掉这个it所指的子句
                        while (it < end) {
                            *it2 = *it;
                            it2++;
                            it++;
                        }
                        SASSERT(it2 <= end);
                        w.set_end_clause(it2);//设置l watch的子句的最后一个为it2
                        SASSERT(is_empty_clause(cls));
                        set_conflict(b_justification(cls));//该子句是冲突子句
                        return false;
                    }
                    else {
                        // PROPAGATION 传播
                        SASSERT(first_lit_val == l_undef);//0号位的文字要是未赋值的
                        SASSERT(get_assignment(first_lit) == l_undef);
                        SASSERT(is_unit_clause(cls));//验证cls是一个单元子句
                        *it2 = *it;
                        it2++; // keep clause 保留该子句，因为l依然watch该子句，因为cls中目前只有一个非false文字
                        m_stats.m_num_propagations++;//传播数量加一
                        // It is safe to call assign_core instead of assign because first_lit is unassigned 可以安全地调用assign_core而非assign因为第一个未赋值
                        assign_core(first_lit, b_justification(cls));
                        if (m_fparams.m_relevancy_lemma && cls->is_lemma()) {//如果cls是lemma并且参数中使用了相关性lemma
                            expr * e = bool_var2expr(first_lit.var());
                            // IMPORTANT: this kind of propagation asserts negative literals of the form (= A1 A2) where
                            // A1 and A2 are array terms. So, it may be interesting to disable it for array eqs.
                            //if (!(m.is_eq(e) && m.get_sort(to_app(e)->get_arg(0))->get_family_id() == m.get_family_id("array")))
                            //这种传播 断言了 形如（= A1 A2）的负文字，其中A1和A2是数组项。所以对数组等式禁用它可能很有趣
                            mark_as_relevant(e);
                        }
                    }
                found_watch:;
                }
            }
            SASSERT(it2 <= end);
            w.set_end_clause(it2);
        }
        return true;
    }

    /**
       \brief Push a new equality for theory th, into the theory equality propagation queue. 为理论th，将一个新的等式添加到等式传播队列中
    */
    void context::push_new_th_eq(theory_id th, theory_var lhs, theory_var rhs) {
        SASSERT(lhs != rhs);
        SASSERT(lhs != null_theory_var);
        SASSERT(rhs != null_theory_var);
        SASSERT(th != null_theory_id);
        SASSERT(get_theory(th)->get_enode(lhs) != get_theory(th)->get_enode(rhs));
        m_th_eq_propagation_queue.push_back(new_th_eq(th, lhs, rhs));
    }

    /**
       \brief Push a new disequality for theory th, into the theory disequality propagation queue. 为理论th，将一个新的不等式添加到不等式传播队列中
    */
    void context::push_new_th_diseq(theory_id th, theory_var lhs, theory_var rhs) {
        SASSERT(lhs != rhs);
        SASSERT(lhs != null_theory_var);
        SASSERT(rhs != null_theory_var);
        SASSERT(th != null_theory_id);
        theory * t = get_theory(th);
        if (t->get_enode(lhs)->is_interpreted() && t->get_enode(rhs)->is_interpreted())
            return;
        TRACE("add_diseq",
              tout << "#" << t->get_enode(lhs)->get_owner_id() << " != "
              << "#" << t->get_enode(rhs)->get_owner_id() << "\n";);

        m_th_diseq_propagation_queue.push_back(new_th_eq(th, lhs, rhs));//不等式传播队列中添加一个不等式，是以等式的形式存储
    }
    //在add_eq中被调用，加入到trail中
    class add_eq_trail : public trail<context> {
        enode * m_r1;
        enode * m_n1;
        unsigned m_r2_num_parents;
    public:
        add_eq_trail(enode * r1, enode * n1, unsigned r2_num_parents):
            m_r1(r1),
            m_n1(n1),
            m_r2_num_parents(r2_num_parents) {
        }

        void undo(context & ctx) override {
            ctx.undo_add_eq(m_r1, m_n1, m_r2_num_parents);
        }
    };

    /**
       \brief Add the equality n1 = n2 with justification js into the logical context.
       添加带有证明js的等式n1=n2到逻辑context中
       会选择n1和n2所在的较大的分支，然后将较小的分支中的所有enode都合并到较大的分支中去
       结果是n1 -> ... -> r1  n2 -> ... -> r2合并成r1 -> ..  -> n1 -> n2 -> ... -> r2
        在propagate_bool_var_enode，propogate_eqs，propagate_atoms中被调用
    */
    void context::add_eq(enode * n1, enode * n2, eq_justification js) {
        unsigned old_trail_size = m_trail_stack.size();
        scoped_suspend_rlimit _suspend_cancel(m.limit());

        try {
            TRACE("add_eq", tout << "assigning: #" << n1->get_owner_id() << " = #" << n2->get_owner_id() << "\n";);
            TRACE("add_eq_detail", tout << "assigning\n" << enode_pp(n1, *this) << "\n" << enode_pp(n2, *this) << "\n";
                  tout << "kind: " << js.get_kind() << "\n";);
            SASSERT(m.get_sort(n1->get_owner()) == m.get_sort(n2->get_owner()));

            m_stats.m_num_add_eq++;
            enode * r1 = n1->get_root();//r1，r2分别是n1和n2的根
            enode * r2 = n2->get_root();


            if (r1 == r2) {//如果两个已经属于同一个等价类，即两者的根相同，则是一个多余约束
                TRACE("add_eq", tout << "redundant constraint.\n";);
                return;
            }
            IF_VERBOSE(20, verbose_stream() << "merge " << mk_bounded_pp(n1->get_owner(), m) << " " << mk_bounded_pp(n2->get_owner(), m) << "\n");

            if (r1->is_interpreted() && r2->is_interpreted()) {//如果r1和r2都被解释了，则说明产生冲突
                TRACE("add_eq", tout << "interpreted roots conflict.\n";);
                set_conflict(mk_justification(eq_conflict_justification(n1, n2, js)));
                return;
            }

            // Swap r1 and r2:
            //  1. if the "equivalence" class of r1 is bigger than the equivalence class of r2
            //  OR
            //  2. r1 is interpreted but r2 is not.
            //交换r1和r2如果：r1的等价类 大于 r2的等价类；
            //r1被解释了但是r2没有，这种情况用来强迫以下不变量：如果一个类包含类一个已解释enode 则 其根也是被解释的
            //
            // The second condition is used to enforce the invariant that if a class contain
            // an interpreted enode then the root is also interpreted.
            if ((r1->get_class_size() > r2->get_class_size() && !r2->is_interpreted()) || r1->is_interpreted()) {
                SASSERT(!r2->is_interpreted());
                std::swap(n1, n2);
                std::swap(r1, r2);
            }//交换之后r2是更大的根

            TRACE("add_eq", tout << "merging: #" << r1->get_owner_id() << " #" << r2->get_owner_id() <<
                  " n1: #" << n1->get_owner_id() << "\n";);

            // It is necessary to propagate relevancy to other elements of
            // the equivalence class. This is necessary to enforce the invariant
            // in the field m_parent of the enode class.
            //有必要将相关性传播给等价类中的其他元素。  这是在 enode类的m_parent字段中 强迫不变性质 有必要的。
            if (is_relevant(r1)) { // && !m.is_eq(r1->get_owner())) !is_eq HACK
                // NOTE for !is_eq HACK... the !is_eq HACK does not propagate relevancy when two
                // equality enodes are congruent. I tested this optimization because in V1
                // relevancy is not propagated for congruent equalities.
                // This occurs in V2, because we use the congruence table to propagate disequalities
                // efficiently.
                // I disabled this optimization HACK because it breaks invariants in the rest of the code.
                // To use it, I need to go over the code and analyze all affected places.
                //注意：对于!is_eq HACK，当两个等式enode是一致的时，!is_eq不会传播相关性。使用了同余表来高效传播不等式
                mark_as_relevant(r2);
            }
            else if (is_relevant(r2)) { // && !m.is_eq(r2->get_owner())) { // !is_eq HACK
                mark_as_relevant(r1);
            }

            push_trail(add_eq_trail(r1, n1, r2->get_num_parents()));

            m_qmanager->add_eq_eh(r1, r2);


            merge_theory_vars(n2, n1, js);//将n1和n2的根节点的理论变量合并，结果存放在n2的根节点中

            // 'Proof' tree
            // n1 -> ... -> r1
            // n2 -> ... -> r2
            SASSERT(n1->trans_reaches(r1));
            invert_trans(n1);//将n1->...->r1的序列链表反转
            n1->m_trans.m_target        = n2;
            n1->m_trans.m_justification = js;
            n1->m_proof_is_logged   = false;
            SASSERT(r1->trans_reaches(n1));
            // ---------------
            // r1 -> ..  -> n1 -> n2 -> ... -> r2 会把r1一支的enode都连到r2

            remove_parents_from_cg_table(r1);//当合并进等价类时，最小的那个(也就是全等的根)的父亲节点要被从全等表格中移除，因为它的hash编码会改变，也就是r1会被移除

            enode * curr = r1;
            do {
                curr->m_root = r2;
                curr = curr->m_next;
            }
            while(curr != r1);//将r1的所有m_next的元素的root都设为r2，相当于将r1的一条支路上的enode都以r2为根

            SASSERT(r1->get_root() == r2);
            reinsert_parents_into_cg_table(r1, r2, n1, n2, js);

            if (n2->is_bool())//如果n2是bool的，则传播其布尔赋值
                propagate_bool_enode_assignment(r1, r2, n1, n2);

            // Merge "equivalence" classes 合并等价类
            std::swap(r1->m_next, r2->m_next);

            // Update "equivalence" class size 更新等价类大小
            r2->m_class_size += r1->m_class_size;

            CASSERT("add_eq", check_invariant());
        }
        catch (...) {
            // Restore trail size since procedure was interrupted in the middle.
            // If the add_eq_trail remains on the trail stack, then Z3 may crash when the destructor is invoked.
            TRACE("add_eq", tout << "add_eq interrupted. This is unsafe " << m.limit().is_canceled() << "\n";);
            m_trail_stack.shrink(old_trail_size);
            throw;
        }
    }

    /**
       \brief When merging to equivalence classes, the parents of the smallest one (that are congruence roots),
       must be removed from the congruence table since their hash code will change.
       当合并进等价类时，最小的那个(也就是全等的根)的父亲节点要被从全等表格中移除，因为它的hash编码会改变
       在add_eq中调用
    */
    void context::remove_parents_from_cg_table(enode * r1) {
        // Remove parents from the congruence table
        for (enode * parent : enode::parents(r1)) {
            CTRACE("add_eq", !parent->is_marked() && parent->is_cgc_enabled() && parent->is_true_eq() && m_cg_table.contains_ptr(parent), tout << parent->get_owner_id() << "\n";);
            CTRACE("add_eq", !parent->is_marked() && parent->is_cgc_enabled() && !parent->is_true_eq() &&  parent->is_cgr() && !m_cg_table.contains_ptr(parent), 
                   tout << "cgr !contains " << parent->get_owner_id() << " " << mk_pp(parent->get_decl(), m) << "\n";
                   for (enode* n : enode::args(parent))  tout << n->get_root()->get_owner_id() << " " << n->get_root()->hash() << " ";
                   tout << "\n";
                   tout << "contains: " << m_cg_table.contains(parent) << "\n";
                   if (m_cg_table.contains(parent)) {
                       tout << "owner: " << m_cg_table.find(parent)->get_owner_id() << "\n";
                   }
                   m_cg_table.display(tout);
                   );
            CTRACE("add_eq", !parent->is_marked() && parent->is_cgc_enabled() && !parent->is_true_eq() && !parent->is_cgr() &&  m_cg_table.contains_ptr(parent), tout << "!cgr contains " << parent->get_owner_id() << "\n";);
            SASSERT(parent->is_marked() || !parent->is_cgc_enabled() ||  parent->is_true_eq() || parent->is_cgr() == m_cg_table.contains_ptr(parent));
            SASSERT(parent->is_marked() || !parent->is_cgc_enabled() || !parent->is_true_eq() || !m_cg_table.contains_ptr(parent));
            if (!parent->is_marked() && parent->is_cgr() && !parent->is_true_eq()) {
                SASSERT(!parent->is_cgc_enabled() || m_cg_table.contains_ptr(parent));
                parent->set_mark();
                if (parent->is_cgc_enabled()) {
                    m_cg_table.erase(parent);
                    SASSERT(!m_cg_table.contains_ptr(parent));
                }
            }
        }
    }

    /**
       \brief Reinsert the parents of r1 that were removed from the
       cg_table at remove_parents_from_cg_table. Some of these parents will
       become congruent to other enodes, and a new equality will be propagated.
       Moreover, this method is also used for doing equality propagation.

       The parents of r1 that remain as congruence roots are copied to the
       r2->m_parents.

       The n1, n2, js arguments are used to implement dynamic ackermanization.
       js is a justification for n1 and n2 being equal, and the equality n1 = n2 is
       the one that implied r1 = r2.
       将 因为remove_parents_from_cg_table函数 而被从cg_table中移除的r1的父亲节点重新插入，一些此类父亲节点会和其他的enode变得全等，并且一些新等式会被传播，此外该方法也被用来做等式传播
       如果r1的父亲节点还是全等根，则会被复制为r2的父亲节点
       n1, n2, js是用来实现动态ackermanization的参数，js是一个n1和n2相等的证明，并且等式n1=n2是r1=r2推出的
       会在add_eq中被调用
    */
    void context::reinsert_parents_into_cg_table(enode * r1, enode * r2, enode * n1, enode * n2, eq_justification js) {
        enode_vector & r2_parents  = r2->m_parents;
        enode_vector & r1_parents  = r1->m_parents;
        unsigned num_r1_parents = r1_parents.size();
        for (unsigned i = 0; i < num_r1_parents; ++i) {
            enode* parent = r1_parents[i];
            if (!parent->is_marked())
                continue;
            parent->unset_mark();
            if (parent->is_eq()) {
                SASSERT(parent->get_num_args() == 2);
                TRACE("add_eq_bug", tout << "visiting: #" << parent->get_owner_id() << "\n";);
                enode * lhs = parent->get_arg(0);
                enode * rhs = parent->get_arg(1);
                if (lhs->get_root() == rhs->get_root()) {
                    SASSERT(parent->is_true_eq());
                    unsigned expr_id = parent->get_owner_id();
                    bool_var v = get_bool_var_of_id(expr_id);
                    lbool val  = get_assignment(v);
                    if (val != l_true) {
                        if (val == l_false && js.get_kind() == eq_justification::CONGRUENCE)
                            m_dyn_ack_manager.cg_conflict_eh(n1->get_owner(), n2->get_owner());

                        assign(literal(v), mk_justification(eq_propagation_justification(lhs, rhs)));
                    }
                    // It is not necessary to reinsert the equality to the congruence table
                    continue;
                }
            }
            if (parent->is_cgc_enabled()) {
                enode_bool_pair pair = m_cg_table.insert(parent);
                enode * parent_prime = pair.first;
                if (parent_prime == parent) {
                    SASSERT(parent);
                    SASSERT(parent->is_cgr());
                    SASSERT(m_cg_table.contains_ptr(parent));
                    r2_parents.push_back(parent);
                    continue;
                }
                parent->m_cg = parent_prime;
                SASSERT(!m_cg_table.contains_ptr(parent));
                if (parent_prime->m_root != parent->m_root) {
                    bool used_commutativity = pair.second;
                    TRACE("cg", tout << "found new congruence: #" << parent->get_owner_id() << " = #" << parent_prime->get_owner_id()
                          << " used_commutativity: " << used_commutativity << "\n";);
                    push_new_congruence(parent, parent_prime, used_commutativity);
                }
            }
            else {
                // If congruence closure is not enabled for parent, then I just copy it
                // to r2_parents
                r2_parents.push_back(parent);
            }
        }
    }

    /**
       \brief A transitivity 'proof' branch is represented by
       the following sequence starting at n and ending
       at n->get_root.

       N1      = n
       N_{i+1} = N_i->m_trans.m_target
       and, there is an k such that N_k = n->get_root()

       This method will invert this branch.
       一个由如下 从n开始到n->get_root结束的序列 表示的传递证明，通过N_i->m_trans.m_target逐层向上传递直到root，存在一个k是的N_k=n->get_root()
       该方法会反转这个分支，相当于链表反转
       在undo_add_eq和add_eq中被调用
    */
    void context::invert_trans(enode * n) {
        enode * curr                      = n->m_trans.m_target;
        enode * prev                      = n;
        eq_justification js               = n->m_trans.m_justification;
        prev->m_trans.m_target            = nullptr;
        prev->m_trans.m_justification     = null_eq_justification;
        prev->m_proof_is_logged       = false;
        while (curr != nullptr) {
            SASSERT(prev->trans_reaches(n));
            enode * new_curr              = curr->m_trans.m_target;
            eq_justification new_js       = curr->m_trans.m_justification;
            curr->m_trans.m_target        = prev;
            curr->m_trans.m_justification = js;
            curr->m_proof_is_logged   = false;
            prev                          = curr;
            js                            = new_js;
            curr                          = new_curr;
        }
    }

    /**
       \brief Given that r is the root of n, and r contains a theory variable
       for theory th_id, this method returns a theory variable that is 'closer'
       to n in the 'proof branch' n -> ... -> r.

       This method is used to improve the quality of the conflict clauses produced
       by the logical context.

       Consider the following example:

       - Consider the following sequence of equalities:
       n1 = n2 = n3 = n4 = n5 = n6

       - Now, assume that n1 is the root of the equivalence class
       after each merge. So, the 'proof' branch will have the following
       shape:

       n1 <- n2 <- n3 <- n4 <- n5 <- n6

       - Assuming that all nodes are attached to theory variable, then the following
       sequence of equalities is sent to the theory if the method get_closest_var is not used:

       n1 = n2, n1 = n3, n1 = n4, n1 = n5, n1 = n6

       - This sequence is bad, and bad justifications may be produced by theory.
       For example, assume the following arithmetic constraint

       n5 < n6

       For the arithmetic module, the best justification will be:
       n1 = n5, n1 = n6 and n5 < n6

       This justification contains unnecessary 'junk' to justify that n5 = n6.
       That is, it proves n5 = n6 using the proofs for n1 = n5 and n1 = n6.

       When the method get_closest_var is used in the communication with theories,
       the logical context will send the natural sequence of equalities to the theories:

       n1 = n2 = n3 = n4 = n5 = n6

       假设r是n的根，并且r包含了对于理论th_id的理论变量，该方法会返回一个在证明分支(n->...->r)上更靠近n的理论变量
       该方法被用来提升由逻辑context产生的 “冲突子句” 的质量
       考虑如下例子：
       由一系列等式序列n1=n2=...n6，假设在每次合并之后n1是等价类的根，所以证明序列会有如下形状：n1 <- n2 <- n3 <- n4 <- n5 <- n6
       假设所有的节点都连接着理论变量，如果get_closet没有被使用，则下面的等式序列会被交给理论：n1 = n2, n1 = n3, n1 = n4, n1 = n5, n1 = n6，该序列不好，并且理论可能会产生坏的证明。
       例如假设存在如下数值约束：n5 < n6，对于算术理论模块，最好的证明是n1 = n5, n1 = n6 and n5 < n6
       该证明包含了不必要的句子来证明n5=n6，也就是为了证明n5 = n6，用了n1 = n5 and n1 = n6
       如果是用来get_closest_var方法，则逻辑context会交给理论如下自然的等式序列n1 = n2 = n3 = n4 = n5 = n6
       我认为：就是在寻找这条路径上的各个enode，直到找到根，而不需要通过根来传递等式
    */
    theory_var context::get_closest_var(enode * n, theory_id th_id) {
        if (th_id == null_theory_id)
            return null_theory_var;//如果是空理论，则返回空理论变量
        while (n != nullptr) {
            theory_var v = n->get_th_var(th_id);//v是enode 的中理论th_id的理论变量
            if (v != null_theory_var)//如果v不是空理论变量，就返回
                return v;
            n = n->m_trans.m_target;//m_trans是该enode等价于根的证明，通过它更新n
        }
        return null_theory_var;
    }

    /**
       \brief Merge the theory variables of n2->get_root() and n1->get_root(), the result is stored in n2->get_root().
       New th_var equalities are propagated to the theories.
       将n1和n2的根节点的理论变量合并，结果存放在n2的根节点中，新的理论变量等式会传播给理论
       在大多数情况下，一个enode只会和最多一个理论变量联系
       在add_eq中调用

       \remark In most cases, an enode is attached to at most one theory var.
    */
    void context::merge_theory_vars(enode * n2, enode * n1, eq_justification js) {
        enode * r2 = n2->get_root();
        enode * r1 = n1->get_root();
        if (!r1->has_th_vars() && !r2->has_th_vars()) {
            TRACE("merge_theory_vars", tout << "Neither have theory vars #" << n1->get_owner()->get_id() << " #" << n2->get_owner()->get_id() << "\n";);
            return;
        }

        theory_id from_th = null_theory_id;

        if (js.get_kind() == eq_justification::JUSTIFICATION)
            from_th = js.get_justification()->get_from_theory();

        if (r2->m_th_var_list.get_next() == nullptr && r1->m_th_var_list.get_next() == nullptr) {
            // Common case: r2 and r1 have at most one theory var. 常见情况：r2和r1都只有最多一个理论变量
            theory_id  t2 = r2->m_th_var_list.get_id();
            theory_id  t1 = r1->m_th_var_list.get_id();
            theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t2) : r2->m_th_var_list.get_var();
            theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : r1->m_th_var_list.get_var();
            TRACE("merge_theory_vars",
                  tout << "v2: " << v2 << " #" << r2->get_owner_id() << ", v1: " << v1 << " #" << r1->get_owner_id()
                  << ", t2: " << t2 << ", t1: " << t1 << "\n";);
            if (v2 != null_theory_var && v1 != null_theory_var) {//如果v2和v1都不是空理论变量
                if (t1 == t2) {//如果n1，n2的理论相同，并且不是js的理论，则要添加 理论等式 用来传播
                    // only send the equality to the theory, if the equality was not propagated by it.
                    // 只把等式交给理论，如果等式没有被它传播
                    if (t1 != from_th)
                        push_new_th_eq(t1, v2, v1);//添加理论等式
                }
                else {//n1，n2的理论不同
                    // uncommon case: r2 will have two theory_vars attached to it.
                    //不常规的情况，r2会有2个相关的理论变量
                    r2->add_th_var(v1, t1, m_region);//把(v1,t1)元素加到理论变量列表中
                    push_new_th_diseqs(r2, v1, get_theory(t1));//添加理论不等式
                    push_new_th_diseqs(r1, v2, get_theory(t2));
                }
            }
            else if (v1 == null_theory_var && v2 != null_theory_var) {//只有v1是空理论变量
                push_new_th_diseqs(r1, v2, get_theory(t2));
            }
            else if (v1 != null_theory_var && v2 == null_theory_var) {//只有v2是空理论变量
                r2->m_th_var_list.set_var(v1);//把r2的理论变量列表设为v1的
                r2->m_th_var_list.set_id(t1);
                TRACE("merge_theory_vars", tout << "push_new_th_diseqs v1: " << v1 << ", t1: " << t1 << "\n";);
                push_new_th_diseqs(r2, v1, get_theory(t1));
            }
        }
        else {
            // r1 and/or r2 have more than one theory variable.
            //r1或者r2有超过一个理论变量
            TRACE("merge_theory_vars",
                  tout << "#" << r1->get_owner_id() << " == #" << r2->get_owner_id() << "\n";);


            theory_var_list * l2 = r2->get_th_var_list();
            while (l2) {
                theory_id  t2 = l2->get_id();
                theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t2) : l2->get_var();
                SASSERT(v2 != null_theory_var);
                SASSERT(t2 != null_theory_id);
                theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t2) : r1->get_th_var(t2);

                if (v1 != null_theory_var) {
                    // only send the equality to the theory, if the equality was not propagated by it.
                    //只吧等式传播给理论，如果等式没有被它传播
                    if (t2 != from_th)
                        push_new_th_eq(t2, v2, v1);
                }
                else {
                    push_new_th_diseqs(r1, v2, get_theory(t2));
                }
                l2 = l2->get_next();
            }

            theory_var_list * l1 = r1->get_th_var_list();
            while (l1) {
                theory_id  t1 = l1->get_id();
                theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : l1->get_var();
                SASSERT(v1 != null_theory_var);
                SASSERT(t1 != null_theory_id);
                theory_var v2 = r2->get_th_var(t1);
                if (v2 == null_theory_var) {
                    r2->add_th_var(v1, t1, m_region);
                    push_new_th_diseqs(r2, v1, get_theory(t1));
                }
                l1 = l1->get_next();
            }
        }
    }

    /**
       \brief Propagate the boolean assignment when two equivalence classes are merged.
       当2个等价类被合并的时候，传播布尔赋值
       在add_eq中被调用
    */
    void context::propagate_bool_enode_assignment(enode * r1, enode * r2, enode * n1, enode * n2) {
        SASSERT(n1->is_bool());
        SASSERT(n2->is_bool());
        SASSERT(r1->is_bool());
        SASSERT(r2->is_bool());
        if (r2 == m_false_enode || r2 == m_true_enode) {//如果r2是个false或者true的enode
            bool sign = r2 == m_false_enode;//如果r2为false_enode则sign为true
            enode * curr = r1;
            do {
                SASSERT(curr != m_false_enode);//curr不是false_enode
                bool_var v = enode2bool_var(curr);
                literal l(v, sign);
                if (get_assignment(l) != l_true)//如果l的赋值不是真，则给它赋值层真的,也就是把curr对应的值赋值成和r2相同的
                    assign(l, mk_justification(eq_root_propagation_justification(curr)));
                curr = curr->m_next;
            }
            while (curr != r1);//逐个寻找下一个，直到找回到r1
        }
        else {//如果r2不是true或者false
            bool_var v1 = enode2bool_var(n1);
            bool_var v2 = enode2bool_var(n2);
            lbool val1  = get_assignment(v1);//var1和var2表示年n1对应的变量的赋值
            lbool val2  = get_assignment(v2);
            if (val1 != val2) {//如果n1和n2对应的赋值不同就要进行传播
                if (val2 == l_undef)//如果val2未定义就以n2未目标传播，将n1对应的赋值传给n2
                    propagate_bool_enode_assignment_core(n1, n2);
                else
                    propagate_bool_enode_assignment_core(n2, n1);
            }
        }
    }

    /**
       \brief source and target are boolean enodes, they were proved to be equal,
       and the boolean variable associated with source is assigned. Then,
       copy the assignment to the boolean variables associated with target.
       源和目标是boolean的enode，他们被证实是相同的，并且和源相关的布尔变量是被赋值的，则将赋值复制给目标相关的布尔变量
       在propogate_bool_enode_assignment中被调用
    */
    void context::propagate_bool_enode_assignment_core(enode * source, enode * target) {
        SASSERT(source->is_bool());
        SASSERT(target->is_bool());
        SASSERT(source->get_root() == target->get_root());
        bool_var v_source = enode2bool_var(source);
        lbool    val      = get_assignment(v_source);
        SASSERT(val != l_undef);
        bool     sign     = val == l_false;
        enode * first = target;
        do {
            bool_var v2 = enode2bool_var(target);
            lbool val2  = get_assignment(v2);
            if (val2 != val) {
                if (val2 != l_undef && congruent(source, target) && source->get_num_args() > 0)
                    m_dyn_ack_manager.cg_conflict_eh(source->get_owner(), target->get_owner());
                assign(literal(v2, sign), mk_justification(mp_iff_justification(source, target)));
            }
            target = target->get_next();
        }
        while (first != target);
    }
    //消除add_eq操作
    void context::undo_add_eq(enode * r1, enode * n1, unsigned r2_num_parents) {
        enode * r2 = r1->get_root();
        TRACE("add_eq", tout << "undo_add_eq #" << r1->get_owner_id() << " #" << r2->get_owner_id() << "\n";);

        // restore r2 class size 恢复r2的类大小
        r2->m_class_size -= r1->m_class_size;

        // unmerge "equivalence" classes 分离等价类
        std::swap(r1->m_next, r2->m_next);

        // remove the parents of r1 that remained as congruence roots
        enode_vector::iterator it  = r2->begin_parents();
        enode_vector::iterator end = r2->end_parents();
        it += r2_num_parents;
        for (; it != end; ++it) {
            enode * parent = *it;
            if (parent->is_cgc_enabled()) {
                CTRACE("add_eq", !parent->is_cgr() || !m_cg_table.contains_ptr(parent),
                       tout << "old num_parents: " << r2_num_parents 
                            << "\nnum_parents: " << r2->m_parents.size() 
                            << "\nparent: #" << parent->get_owner_id() 
                            << "\nparents: ";
                       for (enode* p : r2->m_parents) tout << "#" << p->get_owner_id() << " ";
                       display(tout << "\n"););
                SASSERT(parent->is_cgr());
                SASSERT(m_cg_table.contains_ptr(parent));
                m_cg_table.erase(parent);
            }
        }

        enode * curr = r1;
        do {
            curr->m_root = r1;
            curr = curr->m_next;
        }
        while (curr != r1);

        // restore parents of r2
        r2->m_parents.shrink(r2_num_parents);

        // try to reinsert parents of r1 that are not cgr
        for (enode * parent : enode::parents(r1)) {
            TRACE("add_eq_parents", tout << "visiting: #" << parent->get_owner_id() << "\n";);
            if (parent->is_cgc_enabled()) {
                
                enode * cg = parent->m_cg;
                if (!parent->is_true_eq() &&
                    (parent == cg ||           // parent was root of the congruence class before and after the merge
                     !congruent(parent, cg)    // parent was root of the congruence class before but not after the merge
                     )) {
                    enode_bool_pair p = m_cg_table.insert(parent);
                    parent->m_cg = p.first;
                }
            }
        }

        // restore theory vars
        if (r2->m_th_var_list.get_next() == nullptr) {
            // common case: r2 has at most one variable
            theory_var v2 = r2->m_th_var_list.get_var();
            if (v2 != null_theory_var) {
                theory_id  t2 = r2->m_th_var_list.get_id();
                if (get_theory(t2)->get_enode(v2)->get_root() != r2) {
                    SASSERT(get_theory(t2)->get_enode(v2)->get_root() == r1);
                    r2->m_th_var_list.set_var(null_theory_var); //remove variable from r2
                    r2->m_th_var_list.set_id(null_theory_id);
                }
            }
        }
        else {
            restore_theory_vars(r2, r1);
        }

        // 'Proof' tree
        // r1 -> ..  -> n1 -> n2 -> ... -> r2
        SASSERT(r1->trans_reaches(r2));
        SASSERT(r1->trans_reaches(n1));
        n1->m_trans.m_target        = nullptr;
        n1->m_trans.m_justification = null_eq_justification;
        n1->m_proof_is_logged   = false;
        invert_trans(r1);
        // ---------------
        // n1 -> ... -> r1
        // n2 -> ... -> r2
        SASSERT(n1->trans_reaches(r1));
        SASSERT(r1->m_trans.m_target == 0);

        CASSERT("add_eq", check_invariant());
    }

    /**
       \brief Auxiliary method for undo_add_eq.
       It restores the theory variables of a given root enode.
       This method deletes any theory variable v2 of r2 (for a theory t2)
       whenever:

       get_theory(t2)->get_enode(v2)->get_root() != r2

       That is, v2 is not equivalent to r2 anymore.
       恢复理论变量
       为undo_add_eq设计的附加方法，它恢复了给定 根 enode的理论变量
       该方法删除了r2的任意理论变量v2（对于理论t2），当t2的enode的根不等于r2时，也就是v2不再等价于r2
       在undo_add_eq中被调用
    */
    void context::restore_theory_vars(enode * r2, enode * r1) {
        SASSERT(r2->get_root() == r2);
        theory_var_list * new_l2  = nullptr;
        theory_var_list * l2      = r2->get_th_var_list();//r2是根，通过r2可以得到理论变量列表
        while (l2) {
            theory_var v2 = l2->get_var();//通过l2获取一个理论变量v2
            theory_id t2  = l2->get_id();

            if (get_theory(t2)->get_enode(v2)->get_root() != r2) {//如果t2中的v2的根不是r2
                SASSERT(get_theory(t2)->get_enode(v2)->get_root() == r1);//要保证t2中v2的根是r1
                l2 = l2->get_next();
            }
            else {
                if (new_l2) {
                    new_l2->set_next(l2);
                    new_l2 = l2;
                }
                else {
                    r2->m_th_var_list = *l2;
                    new_l2 = &(r2->m_th_var_list);
                }
                l2 = l2->get_next();
            }
        }

        if (new_l2) {
            new_l2->set_next(nullptr);
        }
        else {
            r2->m_th_var_list.set_var(null_theory_var);
            r2->m_th_var_list.set_next(nullptr);
        }
    }

    /**
       \brief This method is invoked when a new disequality is asserted.
       The disequality is propagated to the theories.
       该方法在一个新的不等式(n1!=n2)被断言的时候调用，不等式被传播到理论
       该方法在propagate_atoms方法中被调用，向不等式传播队列中添加相应的不等式
       注意此处添加进的队列是“理论”不等式队列
       在propogate_atom中调用
    */
    bool context::add_diseq(enode * n1, enode * n2) {
        enode * r1 = n1->get_root();
        enode * r2 = n2->get_root();
        TRACE("add_diseq", tout << "assigning: #" << n1->get_owner_id() << " != #" << n2->get_owner_id() << "\n";
              tout << mk_ll_pp(n1->get_owner(), m) << " != ";
              tout << mk_ll_pp(n2->get_owner(), m) << "\n";
              tout << mk_ll_pp(r1->get_owner(), m) << " != ";
              tout << mk_ll_pp(r2->get_owner(), m) << "\n";
              );

        DEBUG_CODE(
            push_trail(push_back_trail<context, enode_pair, false>(m_diseq_vector));
            m_diseq_vector.push_back(enode_pair(n1, n2)););

        if (r1 == r2) {
            TRACE("add_diseq_inconsistent", tout << "add_diseq #" << n1->get_owner_id() << " #" << n2->get_owner_id() << " inconsistency, scope_lvl: " << m_scope_lvl << "\n";);
            //return false;

            theory_id  t1 = r1->m_th_var_list.get_id();
            if (t1 == null_theory_id) return false;
            return get_theory(t1)->use_diseqs();
        }

        // Propagate disequalities to theories 将不等式传播给理论
        if (r1->m_th_var_list.get_next() == nullptr && r2->m_th_var_list.get_next() == nullptr) {
            // common case: r2 and r1 have at most one theory var. 常规情况：r2和r1有最多一个理论变量
            theory_id  t1 = r1->m_th_var_list.get_id();
            theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : r1->m_th_var_list.get_var();
            theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t1) : r2->m_th_var_list.get_var();
            TRACE("add_diseq", tout << "one theory diseq\n";
                  tout << v1 << " != " << v2 << "\n";
                  tout << "th1: " << t1 << " th2: " << r2->m_th_var_list.get_id() << "\n";
                  );
            if (t1 != null_theory_id && v1 != null_theory_var && v2 != null_theory_var &&
                t1 == r2->m_th_var_list.get_id()) {
                if (get_theory(t1)->use_diseqs())
                    push_new_th_diseq(t1, v1, v2);//将该不等式添加到不等式传播队列中
            }
        }
        else {//r1的理论变量是一个list，而非当个变量
            theory_var_list * l1 = r1->get_th_var_list();
            while (l1) {
                theory_id  t1 = l1->get_id();
                theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : l1->get_var();
                theory * th   = get_theory(t1);
                TRACE("add_diseq", tout << m.get_family_name(t1) << "\n";);
                if (th->use_diseqs()) {
                    theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t1) : r2->get_th_var(t1);
                    if (v2 != null_theory_var)
                        push_new_th_diseq(t1, v1, v2);//逐个将不等式添加到不等式传播队列中
                }
                l1 = l1->get_next();
            }
        }
        return true;
    }

    /**
       \brief Return true if n1 and n2 are known to be disequal in the logical
       context.
       如果n1和n2已知在逻辑context中不等
    */
    bool context::is_diseq(enode * n1, enode * n2) const {
        SASSERT(m.get_sort(n1->get_owner()) == m.get_sort(n2->get_owner()));
        context * _this = const_cast<context*>(this);
        if (!m_is_diseq_tmp) {
            app * eq       = m.mk_eq(n1->get_owner(), n2->get_owner());
            m.inc_ref(eq);
            _this->m_is_diseq_tmp = enode::mk_dummy(m, m_app2enode, eq);
        }
        else if (m.get_sort(m_is_diseq_tmp->get_owner()->get_arg(0)) != m.get_sort(n1->get_owner())) {
            m.dec_ref(m_is_diseq_tmp->get_owner());
            app * eq = m.mk_eq(n1->get_owner(), n2->get_owner());
            m.inc_ref(eq);
            m_is_diseq_tmp->m_func_decl_id = UINT_MAX;
            m_is_diseq_tmp->m_owner = eq;
        }
        m_is_diseq_tmp->m_args[0] = n1;
        m_is_diseq_tmp->m_args[1] = n2;
        SASSERT(m_is_diseq_tmp->get_num_args() == 2);
        enode * r = m_cg_table.find(m_is_diseq_tmp);
        SASSERT((r != 0) == m_cg_table.contains(m_is_diseq_tmp));
        TRACE("is_diseq", tout << "r: " << r << "\n";);
        if (r) {
            SASSERT(r->is_eq());
            literal l = enode2literal(r->get_root());
            // SASSERT(result == is_diseq_slow(n1, n2));
            return l != true_literal && (l == false_literal || (is_relevant(l) && get_assignment(l) == l_false));
        }
        CTRACE("is_diseq_bug", is_diseq_slow(n1, n2), tout << "#" << n1->get_owner_id() << " #" << n2->get_owner_id() << "\n";);
        return false;
    }

    /**
       \brief Slow version of is_diseq
       is_diseq的慢速版本
    */
    bool context::is_diseq_slow(enode * n1, enode * n2) const {
        if (n1->get_num_parents() > n2->get_num_parents())
            std::swap(n1, n2);
        for (enode * parent : enode::parents(n1)) {
            if (parent->is_eq() && is_relevant(parent->get_owner()) && get_assignment(enode2bool_var(parent)) == l_false &&
                ((parent->get_arg(0)->get_root() == n1->get_root() && parent->get_arg(1)->get_root() == n2->get_root()) ||
                 (parent->get_arg(1)->get_root() == n1->get_root() && parent->get_arg(0)->get_root() == n2->get_root()))) {
                TRACE("is_diseq_bug", tout << "parent: #" << parent->get_owner_id() << ", parent->root: #" <<
                      parent->get_root()->get_owner_id() << " assignment(parent): " << get_assignment(enode2bool_var(parent)) <<
                      " args: #" << parent->get_arg(0)->get_owner_id() << " #" << parent->get_arg(1)->get_owner_id() << "\n";);
                return true;
            }
        }
        return false;
    }

#define SMALL_NUM_PARENTS 3

    bool context::is_ext_diseq(enode * n1, enode * n2, unsigned depth) {
        enode * r1 = n1->get_root();
        enode * r2 = n2->get_root();
        if (r1 == r2)
            return false;
        if (r1->is_interpreted() && r2->is_interpreted())
            return true;
        if (is_diseq(n1, n2))
            return true;
        if (r1->get_num_parents() > r2->get_num_parents()) {
            std::swap(n1, n2);
            std::swap(r1, r2);
        }
        if (depth == 0)
            return false;
        if (r1->get_num_parents() < SMALL_NUM_PARENTS) {
            TRACE("is_ext_diseq", tout << enode_pp(n1, *this) << " " << enode_pp(n2, *this) << " " << depth << "\n";);
            for (enode * p1 : enode::parents(r1)) {
                if (!is_relevant(p1))
                    continue;
                if (p1->is_eq())
                    continue;
                if (!p1->is_cgr())
                    continue;
                func_decl * f     = p1->get_decl();
                TRACE("is_ext_diseq", tout << "p1: " << enode_pp(p1, *this) << "\n";);
                unsigned num_args = p1->get_num_args();
                for (enode * p2 : enode::parents(r2)) {
                    if (!is_relevant(p2))
                        continue;
                    if (p2->is_eq())
                        continue;
                    if (!p2->is_cgr())
                        continue;
                    TRACE("is_ext_diseq", tout << "p2: " << enode_pp(p2, *this) << "\n";);
                    if (p1->get_root() != p2->get_root() && p2->get_decl() == f && p2->get_num_args() == num_args) {
                        unsigned j = 0;
                        for (j = 0; j < num_args; j++) {
                            enode * arg1 = p1->get_arg(j)->get_root();
                            enode * arg2 = p2->get_arg(j)->get_root();
                            if (arg1 == arg2)
                                continue;
                            if ((arg1 == r1 || arg1 == r2) &&
                                (arg2 == r1 || arg2 == r2))
                                continue;
                            break;
                        }
                        if (j == num_args) {
                            TRACE("is_ext_diseq", tout << "found parents: " << enode_pp(p1, *this) << " " << enode_pp(p2, *this) << "\n";);
                            if (is_ext_diseq(p1, p2, depth - 1))
                                return true;
                        }
                    }
                }
            }
        }
        else {
            if (depth >= m_almost_cg_tables.size()) {
                unsigned old_sz = m_almost_cg_tables.size();
                m_almost_cg_tables.resize(depth+1);
                for (unsigned i = old_sz; i < depth + 1; i++)
                    m_almost_cg_tables[i] = alloc(almost_cg_table);
            }
            almost_cg_table & table = *(m_almost_cg_tables[depth]);
            table.reset(r1, r2);
            for (enode * p1 : enode::parents(r1)) {
                if (!is_relevant(p1))
                    continue;
                if (p1->is_eq())
                    continue;
                if (!p1->is_cgr())
                    continue;
                table.insert(p1);
            }
            if (table.empty())
                return false;
            for (enode * p2 : enode::parents(r2)) {
                if (!is_relevant(p2))
                    continue;
                if (p2->is_eq())
                    continue;
                if (!p2->is_cgr())
                    continue;
                list<enode*> * ps = table.find(p2);
                while (ps) {
                    enode * p1 = ps->head();
                    if (p1->get_root() != p2->get_root() && is_ext_diseq(p1, p2, depth - 1))
                        return true;
                    ps = ps->tail();
                }
            }
        }
        return false;
    }

    /**
       \brief Return an enode n congruent to (f args). If there is no such enode in the E-graph, then return 0.
        返回一个一致于func_decl f的enode n。如果在E-graph中不存在这样的enode，则返回0
     */
    enode * context::get_enode_eq_to(func_decl * f, unsigned num_args, enode * const * args) {
        enode * tmp = m_tmp_enode.set(f, num_args, args);
        enode * r   = m_cg_table.find(tmp);
#ifdef Z3DEBUG
        if (r != nullptr) {
            SASSERT(r->get_owner()->get_decl() == f);
            SASSERT(r->get_num_args() == num_args);
            if (r->is_commutative()) {
                // TODO
            }
            else {
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg   = r->get_owner()->get_arg(i);
                    SASSERT(e_internalized(arg));
                    enode * _arg = get_enode(arg);
                    CTRACE("eq_to_bug", args[i]->get_root() != _arg->get_root(),
                           tout << "#" << args[i]->get_expr_id() << " #" << args[i]->get_root()->get_expr_id()
                           << " #" << _arg->get_expr_id() << " #" << _arg->get_root()->get_expr_id() << "\n";
                           tout << "#" << r->get_expr_id() << "\n";
                           display(tout););
                    SASSERT(args[i]->get_root() == _arg->get_root());
                }
            }
        }
#endif
        return r;
    }

    /**
       \brief Process the equality propagation queue.
       处理等式传播队列，assign_eq会给该队列添加一个元素， 逐个遍历 m_eq_propagation_queue 队列中的等式，调用add_eq函数将等式添加到context中
       该队列中的元素是来自于assign_eq方法
       在propogate中调用
       （注意区分等式 和 理论等式）

       \remark The method assign_eq adds a new entry on this queue.
    */
    bool context::propagate_eqs() {
        unsigned i = 0;
        for (; i < m_eq_propagation_queue.size() && !get_cancel_flag(); i++) {
            new_eq & entry = m_eq_propagation_queue[i];
            add_eq(entry.m_lhs, entry.m_rhs, entry.m_justification);
            if (inconsistent()) {
                m_eq_propagation_queue.reset();
                return false;
            }
        }
        m_eq_propagation_queue.reset();
        return true;
    }

    /**
       \brief Process equalities, theory atoms, etc.
       处理 等式，理论原子等，逐个遍历原子传播队列中的文字，进行enode传播，等式/不等式传播 在propogate中调用
    */
    bool context::propagate_atoms() {
        SASSERT(!inconsistent());
        CTRACE("propagate_atoms", !m_atom_propagation_queue.empty(), tout << m_atom_propagation_queue << "\n";);
        for (unsigned i = 0; i < m_atom_propagation_queue.size() && !get_cancel_flag(); i++) {//逐个遍历 原子传播队列 中的文字
            SASSERT(!inconsistent());
            literal  l = m_atom_propagation_queue[i];
            bool_var v = l.var();
            bool_var_data & d = get_bdata(v);
            lbool val  = get_assignment(v);
            TRACE("propagate_atoms", tout << "propagating atom, #" << bool_var2expr(v)->get_id() << ", is_enode(): " << d.is_enode()
                  << " tag: " << (d.is_eq()?"eq":"") << (d.is_theory_atom()?"th":"") << (d.is_quantifier()?"q":"") << " " << l << "\n";);
            SASSERT(val != l_undef);//l不能是未赋值的
            if (d.is_enode())
                propagate_bool_var_enode(v);//如果该文字对应的是enode，则传播 赋给v的真值 到 与v相关的enode（应该是等价类的传播）
            if (inconsistent())
                return false;//如果不一致直接返回冲突 false
            if (d.is_eq()) {//如果d代表的是eq，则val是true代表是等式，false是代表不等式
                app * n   = to_app(m_bool_var2expr[v]);
                SASSERT(m.is_eq(n));
                expr * lhs = n->get_arg(0);
                expr * rhs = n->get_arg(1);
                if (m.is_bool(lhs)) {
                    // no-op
                }
                else if (val == l_true) {//添加等式到等式传播队列中
                    add_eq(get_enode(lhs), get_enode(rhs), eq_justification(l));
                }
                else {//添加不等式到不等式传播队列中
                    TRACE("add_diseq", display_eq_detail(tout, bool_var2enode(v)););
                    if (!add_diseq(get_enode(lhs), get_enode(rhs)) && !inconsistent()) {
                        literal n_eq = literal(l.var(), true);
                        set_conflict(b_justification(mk_justification(eq_propagation_justification(get_enode(lhs), get_enode(rhs)))), n_eq);
                    }
                }
            }
            else if (d.is_theory_atom()) {
                theory * th = m_theories.get_plugin(d.get_theory());
                SASSERT(th);
                th->assign_eh(v, val == l_true);                
            }
            else if (d.is_quantifier()) {
                // Remark: when RELEVANCY_LEMMA is true, a quantifier can be asserted to false and marked as relevant.
                // This happens when a quantifier is part of a lemma (conflict-clause), and this conflict clause
                // becomes an unit-clause and the remaining literal is the negation of a quantifier.
                CTRACE("assign_quantifier_bug", get_assignment(v) != l_true,
                       tout << "#" << bool_var2expr(v)->get_id() << " val: " << get_assignment(v) << "\n";
                       tout << mk_pp(bool_var2expr(v), m) << "\n";
                       display(tout););
                SASSERT(is_quantifier(m_bool_var2expr[v]));
                if (get_assignment(v) == l_true) {
                    // All universal quantifiers have positive polarity in the input formula.
                    // So, we can ignore quantifiers assigned to false.
                    assign_quantifier(to_quantifier(m_bool_var2expr[v]));
                }
            }
            if (inconsistent())
                return false;
        }
        m_atom_propagation_queue.reset();
        return true;
    }
    //在set_var_theory中调用
    class set_var_theory_trail : public trail<context> {
        bool_var m_var;
    public:
        set_var_theory_trail(bool_var v):m_var(v) {}
        void undo(context & ctx) override {
            bool_var_data & d = ctx.m_bdata[m_var];
            d.reset_notify_theory();
        }
    };
    //为变量设置理论号，为布尔变量v的m_bdata 设置相应的理论号
    void context::set_var_theory(bool_var v, theory_id tid) {
        SASSERT(get_var_theory(v) == null_theory_var);
        SASSERT(tid > 0 && tid <= 255);//理论号在1～255之间
        SASSERT(get_intern_level(v) <= m_scope_lvl);
        if (m_scope_lvl > get_intern_level(v))
            push_trail(set_var_theory_trail(v));
        bool_var_data & d = m_bdata[v];
        d.set_notify_theory(tid);
    }

    /**
       \brief Propagate the truth value assigned to v, to the enode
       associated with v.  Let n be the enode associated with v. Then,
       this method merges n = true_term (n = false_term) if v was
       assigned to true (false).
       传播赋值给v的真值 到 与v相关的enode（应该是等价类的传播）
       设n是与v相关的enode，则如果v被赋值为true，该方法将合并n=true_term
       在propogate_atom中被调用
    */
    void context::propagate_bool_var_enode(bool_var v) {
        SASSERT(get_assignment(v) != l_undef);//该变量v目前已经被赋值了
        SASSERT(get_bdata(v).is_enode());
        lbool val  = get_assignment(v);
        TRACE("propagate_bool_var_enode_bug", tout << "var: " << v << " #" << bool_var2expr(v)->get_id() << "\n";);
        SASSERT(v < static_cast<int>(m_b_internalized_stack.size()));
        enode * n  = bool_var2enode(v);//n是与v相关的enode

        CTRACE("mk_bool_var", !n, tout << "No enode for " << v << "\n";);
        bool sign  = val == l_false;
        if (n->merge_tf())
            add_eq(n, sign ? m_false_enode : m_true_enode, eq_justification(literal(v, sign)));
        if (watches_fixed(n)) 
            assign_fixed(n, sign ? m.mk_false() : m.mk_true(), literal(v, sign));
        enode * r = n->get_root();
        if (r == m_true_enode || r == m_false_enode)
            return;
        // Move truth value to other elements of the equivalence class if:
        //   1) n is the root of the equivalence class
        //   2) n is not the root, but the variable associated with the root is unassigned.
        //将真值转移到等价类的其他元素中，如果
        //(1)n是等价类的根
        //(2)n不是等价类的根， 但与根关联的变量未被赋值
        if (n == r ||
            !is_relevant(r) || // <<<< added to fix propagation bug.
            get_assignment(enode2bool_var(r)) != val) {
            enode * first = n;
            n = n->get_next();
            while (n != first) {
                bool_var v2 = enode2bool_var(n);
                if (get_assignment(v2) != val)
                    assign(literal(v2, sign), mk_justification(mp_iff_justification(first, n)));
                n = n->get_next();
            }
        }
    }

    /**
       \brief Traverse the disequalities of r's equivalence class, and
       propagate them to the theory.
       遍历r的等价类的不等式，并将他们传播给理论,在merge_theory_vars中被调用
       会调用push_new_th_diseq来向m_th_diseq_propagation_queue队列中加入不等式
    */
    void context::push_new_th_diseqs(enode * r, theory_var v, theory * th) {
        if (!th->use_diseqs()) {
            TRACE("push_new_th_diseqs", tout << m.get_family_name(th->get_id()) << " not using diseqs\n";);
            return;
        }
        theory_id th_id = th->get_id();
        TRACE("push_new_th_diseqs", tout << "#" << r->get_owner_id() << " " << mk_bounded_pp(r->get_owner(), m) << " v" << v << " th: " << th_id << "\n";);
        for (enode * parent : r->get_parents()) {
            CTRACE("parent_bug", parent == 0, tout << "#" << r->get_owner_id() << ", num_parents: " << r->get_num_parents() << "\n"; display(tout););
            if (parent->is_eq()) {
                bool_var bv = get_bool_var_of_id(parent->get_owner_id());
                if (get_assignment(bv) == l_false) {
                    enode * lhs = parent->get_arg(0);
                    enode * rhs = parent->get_arg(1);
                    TRACE("push_new_th_diseqs",
                          tout << "#" << parent->get_owner_id() << " ";
                           tout << "lhs: #" << lhs->get_owner_id() << ", rhs: #" << rhs->get_owner_id() <<
                           ", lhs->root: #" << lhs->get_root()->get_owner_id() << ", rhs->root: #" << rhs->get_root()->get_owner_id() <<
                           ", r: #" << r->get_owner_id() << ", r->root: #" << r->get_root()->get_owner_id() << "\n";
                          );
                    CTRACE("push_new_th_diseqs", lhs->get_root() != r->get_root() && rhs->get_root() != r->get_root(),
                           tout << "lhs: #" << lhs->get_owner_id() << ", rhs: #" << rhs->get_owner_id() <<
                           ", lhs->root: #" << lhs->get_root()->get_owner_id() << ", rhs->root: #" << rhs->get_root()->get_owner_id() <<
                           ", r: #" << r->get_owner_id() << ", r->root: #" << r->get_root()->get_owner_id() << "\n";
                          display(tout););
                    SASSERT(lhs->get_root() == r->get_root() || rhs->get_root() == r->get_root());
                    if (rhs->get_root() == r->get_root())
                        std::swap(lhs, rhs);
                    enode * rhs_root   = rhs->get_root();
                    theory_var rhs_var = m_fparams.m_new_core2th_eq ? get_closest_var(rhs, th_id) : rhs_root->get_th_var(th_id);
                    if (m_fparams.m_new_core2th_eq) {
                        theory_var _v = get_closest_var(lhs, th_id);
                        if (_v != null_theory_var)
                            v = _v;
                    }
                    if (rhs_var != null_theory_var && v != rhs_var /* if v == rhs_var then the context will detect the inconsistency. */)//如果v==rhs_var则会检测到不一致
                        push_new_th_diseq(th_id, v, rhs_var);
                }
            }
        }
    }

    /**
       \brief Return the truth assignment for an expression
       that is attached to a boolean variable.
       返回一个 与布尔变量相联系的 表达式的真值，该表达式必须与一个布尔变量相关联

       \pre The expression must be attached to a boolean variable.
    */
    inline lbool context::get_assignment_core(expr * n) const {
        CTRACE("get_assignment_bug", !b_internalized(n), tout << "n:\n" << mk_pp(n, m) << "\n"; display(tout););
        SASSERT(b_internalized(n));
        unsigned id  = n->get_id();
        bool_var var = get_bool_var_of_id(id);
        SASSERT(var != null_bool_var);
        return get_assignment(var);
    }

    /**
       \brief Return the truth assignment for an expression.
       If the expression is a not-application, then its child
       is inspected instead.
       返回一个表达式的真值，如果该表达式是一个not-application，则检测他的子节点
    */
    lbool context::get_assignment(expr * n) const {
        if (m.is_false(n))
            return l_false;
        expr* arg = nullptr;
        if (m.is_not(n, arg))
            return ~get_assignment_core(arg);
        return get_assignment_core(n);
    }
    //此处的n未必是和bool变量相关联的，若无关联则返回undef
    lbool context::find_assignment(expr * n) const {
        if (m.is_false(n))
            return l_false;
        expr* arg = nullptr;
        if (m.is_not(n, arg)) {
            if (b_internalized(arg))
                return ~get_assignment_core(arg);
            return l_undef;
        }
        if (b_internalized(n))
            return get_assignment(n);
        return l_undef;
    }

    /**
       \brief Return the assignment of a 'boolean' enode.
       If the enode is not boolean, then return l_undef.
       返回一个bool enode的赋值，如果该enode不是bool的，则返回undef
    */
    lbool context::get_assignment(enode * n) const {
        expr * owner = n->get_owner();
        if (!m.is_bool(owner))
            return l_undef;
        if (n == m_false_enode)
            return l_false;
        bool_var v = get_bool_var_of_id(owner->get_id());
        CTRACE("missing_propagation", v == null_bool_var, tout << mk_pp(owner, m) << "\n";);
        return get_assignment(v);
    }

    /**
       \brief Return set of assigned literals as expressions.
       返回已赋值文字的值 作为表达式返回，逐个遍历赋值文字，将其转为expr_ref，收集于expr_ref_vector assignments中
    */
    void context::get_assignments(expr_ref_vector& assignments) {
        for (literal lit : m_assigned_literals) {
            expr_ref e(m);
            literal2expr(lit, e);
            assignments.push_back(std::move(e));
        }
    }
    //无调用
    void context::relevant_eh(expr * n) {
        if (b_internalized(n)) {
            bool_var v        = get_bool_var(n);
            bool_var_data & d = get_bdata(v);
            SASSERT(relevancy());
            // Quantifiers are only asserted when marked as relevant.
            // Other atoms are only asserted when marked as relevant if relevancy_lvl >= 2
            if (d.is_atom() && (d.is_quantifier() || relevancy_lvl() >= 2)) {
                lbool val  = get_assignment(v);
                if (val != l_undef)
                    m_atom_propagation_queue.push_back(literal(v, val == l_false));
            }
        }
        TRACE("propagate_relevancy", tout << "marking as relevant:\n" << mk_bounded_pp(n, m) << " " << m_scope_lvl << "\n";);
        m_case_split_queue->relevant_eh(n);

        if (is_app(n)) {
            if (e_internalized(n)) {
                SASSERT(relevancy());
                enode * e = get_enode(n);
                m_qmanager->relevant_eh(e);
            }

            theory * propagated_th = nullptr;
            family_id fid = to_app(n)->get_family_id();
            if (fid != m.get_basic_family_id()) {
                theory * th = get_theory(fid);
                if (th != nullptr) {
                    th->relevant_eh(to_app(n));
                    propagated_th = th; // <<< mark that relevancy_eh was already invoked for theory th.
                }
            }

            if (e_internalized(n)) {
                enode *           e = get_enode(n);
                theory_var_list * l = e->get_th_var_list();
                while (l) {
                    theory_id  th_id = l->get_id();
                    theory *   th    = get_theory(th_id);
                    // I don't want to invoke relevant_eh twice for the same n.
                    if (th != propagated_th)
                        th->relevant_eh(to_app(n));
                    l = l->get_next();
                }
            }
        }
    }

    /**
       \brief Propagate relevancy using the queue of new assigned literals
       located at [qhead, m_assigned_literals.size()).
        用位于[qhead, m_assigned_literals.size())的新赋值的文字队列，来传播相关性
        对 从qhead开始的所有被赋值的文字 传播相关性
    */
    void context::propagate_relevancy(unsigned qhead) {
        if (!relevancy())
            return;
        unsigned sz = m_assigned_literals.size();//已赋值的文字的数目
        while (qhead < sz) {//遍历[qhead, m_assigned_literals.size())，从旧的m_head开始遍历所有已经赋值的文字
            literal l      = m_assigned_literals[qhead];
            SASSERT(get_assignment(l) == l_true);//赋值的文字一定为真
            qhead++;
            bool_var var   = l.var();//找到刚赋值的文字对应的变量
            expr * n       = m_bool_var2expr[var];//找到该变量对应的表达式n
            m_relevancy_propagator->assign_eh(n, !l.sign());//进行相关性传播，通过assign_eh方法通知相关传播器新的赋值
        }
        m_relevancy_propagator->propagate();//在一系列的assign_eh的通知之后开始使用相关传播器进行传播相关性，该传播针对不同的理论不同
    }
    //理论传播，对每个理论都进行传播，如果出现了不一致，则返回false，如果所有的理论传播都一致，则返回true
    bool context::propagate_theories() {
        for (theory * t : m_theory_set) {//对每个理论逐个传播，出现一个理论传播之后不一致就会返回false
            t->propagate();//理论传播
            if (inconsistent())
                return false;
        }
#if 0
        if (at_search_level() && induction::should_try(*this)) {
            get_induction()();
        }
#endif
        return true;
    }
    //将 等式传播序列 中的所有等式都添加到理论中，进行等式传播，调用相应理论的new_eq_eh句柄 在propogate中被调用
    void context::propagate_th_eqs() {
        for (unsigned i = 0; i < m_th_eq_propagation_queue.size() && !inconsistent(); i++) {//遍历等式传播队列
            new_th_eq curr = m_th_eq_propagation_queue[i];//选取等式传播队列中的第i个等式
            theory * th = get_theory(curr.m_th_id);//找到该等式对应的理论
            SASSERT(th);
            th->new_eq_eh(curr.m_lhs, curr.m_rhs);//向该理论中添加一个等式
            DEBUG_CODE(
                push_trail(push_back_trail<context, new_th_eq, false>(m_propagated_th_eqs));
                m_propagated_th_eqs.push_back(curr););
        }
        m_th_eq_propagation_queue.reset();
    }
    //将 不等式传播队列 中的所有不等式都添加到理论中，进行不等式传播，调用各自理论的new_disq_eh句柄
    void context::propagate_th_diseqs() {
        for (unsigned i = 0; i < m_th_diseq_propagation_queue.size() && !inconsistent(); i++) {
            new_th_eq curr = m_th_diseq_propagation_queue[i];
            theory * th = get_theory(curr.m_th_id);
            SASSERT(th);
            th->new_diseq_eh(curr.m_lhs, curr.m_rhs);
            DEBUG_CODE(
                push_trail(push_back_trail<context, new_th_eq, false>(m_propagated_th_diseqs));
                m_propagated_th_diseqs.push_back(curr););
        }
        m_th_diseq_propagation_queue.reset();
    }
    //如果可以理论传播则返回true，逐个检测每个理论，如果存在一个理论可以传播，就返回true，如果都不可以传播才返回false
    bool context::can_theories_propagate() const {
        for (theory* t : m_theory_set) {
            if (t->can_propagate()) {
                return true;
            }
        }
        return false;
    }
    //判断是否可以继续传播，如果可以返回true，在final_check和propogate中调用
    bool context::can_propagate() const {
        return//满足如下情况之一都是可以继续传播的
            m_qhead != m_assigned_literals.size() ||//如果所有已经赋值的文字都已经被考察
            m_relevancy_propagator->can_propagate() ||//相关性传播非空
            !m_atom_propagation_queue.empty() ||//待传播的原子队列非空
            m_qmanager->can_propagate() ||//理论传播量词
            can_theories_propagate() ||//可以理论传播
            !m_eq_propagation_queue.empty() ||//尚可以传播等式
            !m_th_eq_propagation_queue.empty() ||//尚可以传播理论等式
            !m_th_diseq_propagation_queue.empty();//尚可传播理论不等式
    }

    /**
       \brief retrieve facilities for creating induction lemmas.
       检索用于创建归纳引理的工具。在propagate_relevancy中被调用
     */
    induction& context::get_induction() {
        if (!m_induction) {//如果m_induction不存在，则分配一个
            m_induction = alloc(induction, *this, get_manager());
        }
        return *m_induction;
    }

    /**
       \brief unit propagation.
       Cancelation is not safe during propagation at base level because
       congruences cannot be retracted to a consistent state.
        在底层传播期间取消是不安全的，因为congreuences不能恢复到一致状态

       单元传播
       返回是否需要decide
       如果不一致则返回false，
       如果不能传播了，则返回true，此时需要进行decide操作；或者如果资源耗尽了，就需要跳出走向unknown
       在push，decide，bounded_search，init_assumptions中被调用!!!
     */
    bool context::propagate() {
        TRACE("propagate", tout << "propagating... " << m_qhead << ":" << m_assigned_literals.size() << "\n";);
        while (true) {
            if (inconsistent())//如果已经有不一致，则说明需要回溯再传播，还不需要decide
                return false;
            unsigned qhead = m_qhead;//记录下旧的m_qhead，指向bcp尚未处理的assigned文字，m_qhead会在bcp的过程中变化，而其余传播要从旧的m_qhead开始
            {
                scoped_suspend_rlimit _suspend_cancel(m.limit(), at_base_level());
                if (!bcp())//对bool变量进行传播，如果发生冲突就返回false
                    return false;
                if (!propagate_th_case_split(qhead))//传播理论case_split，如果发生冲突，就返回false，该操作不会改变m_head
                    return false;
                SASSERT(!inconsistent());//在进行了BCP和理论case_split传播之后，如果能走到这里一定是一致的，如果不一致则会在前面传播时return false
                propagate_relevancy(qhead);//传播相关性
                if (inconsistent())
                    return false;
                if (!propagate_atoms())//传播原子 处理等式 原子等
                    return false;
                if (!propagate_eqs())//传播命题层面的等式
                    return false;
                propagate_th_eqs();//传播理论等式
                propagate_th_diseqs();//传播理论不等式
                if (inconsistent())
                    return false;
                if (!propagate_theories())//理论传播
                    return false;
            }
            if (!get_cancel_flag()) {
                scoped_suspend_rlimit _suspend_cancel(m.limit(), at_base_level());
                m_qmanager->propagate();//如果已经取消了，则需要量词传播？
            }
            if (inconsistent())
                return false;
            if (resource_limits_exceeded()) {//如果已经资源耗尽了，则需要将m_qhead恢复到之旧的
                m_qhead = qhead;
                return true;
            }
            if (!can_propagate()) {//如果已经不能传播了，则说明需要decide了，就返回true
                CASSERT("diseq_bug", inconsistent() || check_missing_diseq_conflict());
                CASSERT("eqc_bool", check_eqc_bool_assignment());
                return true;
            }
        }
    }

    //设置冲突，如果不一致就设置冲突为js
    void context::set_conflict(const b_justification & js, literal not_l) {
        if (!inconsistent()) {
            TRACE("set_conflict", display_literal_verbose(tout << m_scope_lvl << " ", not_l); display(tout << " ", js); );
            m_conflict = js;
            m_not_l    = not_l;
        }
    }
    //为量词赋值，在propagate_atoms中被调用
    void context::assign_quantifier(quantifier * q) {
        TRACE("assumption", tout << mk_pp(q, m) << "\n";);
        m_qmanager->assign_eh(q);
    }
    //胖蛋是否包含实例，无调用
    bool context::contains_instance(quantifier * q, unsigned num_bindings, enode * const * bindings) {
        return m_fingerprints.contains(q, q->get_id(), num_bindings, bindings);
    }
    //添加例子，无调用
    bool context::add_instance(quantifier * q, app * pat, unsigned num_bindings, enode * const * bindings, expr* def, unsigned max_generation,
                               unsigned min_top_generation, unsigned max_top_generation, vector<std::tuple<enode *, enode *>> & used_enodes) {
        return m_qmanager->add_instance(q, pat, num_bindings, bindings, def, max_generation, min_top_generation, max_top_generation, used_enodes);
    }
    //重新放缩bool变量的活跃度，无调用
    void context::rescale_bool_var_activity() {
        TRACE("case_split", tout << "rescale\n";);        
        svector<double>::iterator it  = m_activity.begin();
        svector<double>::iterator end = m_activity.end();
        for (; it != end; ++it)
            *it *= INV_ACTIVITY_LIMIT;
        m_bvar_inc *= INV_ACTIVITY_LIMIT;
    }

    /**
       \brief Execute next case split, return false if there are no
       more case splits to be performed.
       执行下一个case split，如果没有case_split可以操作就返回false（启发式）
       仅在bounded_search中被调用，调用了decide_clause
       会在tmp_clause中的所有子句都已经满足的情况下选择一个变量赋值!!!
    */
    bool context::decide() {

        if (at_search_level() && !m_tmp_clauses.empty()) {
            switch (decide_clause()) {//考虑在tmp_clause中决策子句
            case l_true:  // already satisfied 如果tmp_clause中的所有子句已经满足，就执行下面代码
                break;
            case l_undef: // made a decision 如果未定义，就做决策，并返回true，因为已经在decide_clause中做过决策了
                return true;
            case l_false: // inconsistent 如果不一致就说明没有可以case_split的操作，因为在tmp_clause中已经有一个子句不满足了，并且设置了冲突
                return false;
            }
        }
        bool_var var;
        lbool phase = l_undef;
        m_case_split_queue->next_case_split(var, phase);//在tmp_clauses中的所有子句已经满足了的前提下，var是将要选择的变量，phase返回为undef，（其实主要返回的是var，phase总是undef）

        if (var == null_bool_var) {//如果var是空的，意味着没有可以选择的变量
            return false;
        }

        TRACE_CODE({
            static unsigned counter = 0;
            counter++;
            if (counter % 100 == 0) {
                TRACE("activity_profile",
                      for (unsigned i=0; i<get_num_bool_vars(); i++) {
                          tout << get_activity(i) << " ";
                      }
                      tout << "\n";);
            }});

        m_stats.m_num_decisions++;//决策数加一

        push_scope();//创造中间回退点
        TRACE("decide", tout << "splitting, lvl: " << m_scope_lvl << "\n";);

        TRACE("decide_detail", tout << mk_pp(bool_var2expr(var), m) << "\n";);

        bool is_pos;

        if (is_quantifier(m_bool_var2expr[var])) {//如果var是一个量词，重写任何对于量词的决策，将一个量词赋值为false相当于将其设为不相关
            // Overriding any decision on how to assign the quantifier.
            // assigning a quantifier to false is equivalent to make it irrelevant.
            phase = l_false;
        }
        literal l(var, false);//l是var对应的true文字

        if (phase != l_undef) {
            is_pos = phase == l_true;//如果phase不是undef，就判断其是否为true,is_pos用来最后对变量赋值
        }
        else {//phase是undef
            bool_var_data & d = m_bdata[var];
            if (d.try_true_first()) {
                is_pos = true;
            }
            else {
                switch (m_fparams.m_phase_selection) {
                case PS_THEORY: //理论模式
                    if (m_phase_cache_on && d.m_phase_available) {
                        is_pos = m_bdata[var].m_phase;//如果选用来caching技术，则根据m_phase来确定赋值
                        break;
                    }
                    if (!m_phase_cache_on && d.is_theory_atom()) {//如果没有使用caching技术并且是一个理论原子
                        theory * th = m_theories.get_plugin(d.get_theory());
                        lbool th_phase = th->get_phase(var);//通过理论获得该变量的phase
                        if (th_phase != l_undef) {
                            is_pos = th_phase == l_true;
                            break;
                        }
                    }
                    if (track_occs()) {//根据出现次数来定赋值
                        if (m_lit_occs[l.index()] == 0) {
                            is_pos = false;
                            break;
                        }
                        if (m_lit_occs[(~l).index()] == 0) {
                            is_pos = true;
                            break;
                        }
                    }
                    is_pos = m_phase_default;                    
                    break;
                case PS_CACHING:
                case PS_CACHING_CONSERVATIVE://这是默认的方法
                case PS_CACHING_CONSERVATIVE2://根据caching技术来，如果选择了caching，就根据m_phase来确定赋值
                    if (m_phase_cache_on && d.m_phase_available) {
                        TRACE("phase_selection", tout << "using cached value, is_pos: " << m_bdata[var].m_phase << ", var: p" << var << "\n";);
                        is_pos = m_bdata[var].m_phase;
                    }
                    else {
                        TRACE("phase_selection", tout << "setting to false\n";);
                        is_pos = m_phase_default;
                    }
                    break;
                case PS_ALWAYS_FALSE:
                    is_pos = false;
                    break;
                case PS_ALWAYS_TRUE:
                    is_pos = true;
                    break;
                case PS_RANDOM:
                    is_pos = (m_random() % 2 == 0);//如果是随机模式，则任意返回pos的值
                    break;
                case PS_OCCURRENCE: {
                    is_pos = m_lit_occs[l.index()] > m_lit_occs[(~l).index()];//根据出现次数来确定赋值，如果l的出现次数比其非高，就设置为true
                    break;
                }
                default:
                    is_pos = false;
                    UNREACHABLE();
                }
            }
        }

        if (!is_pos) l.neg();//如果phase不是pos，就将l取反，is_pos可以控制相应的赋值
        TRACE("decide", tout << "case split " << l << "\n" << "activity: " << get_activity(var) << "\n";);
        assign(l, b_justification::mk_axiom(), true);//将l设置为真，即赋值l的变量使得l为真
        return true;//此处也做完了决策，返回true表明成功做了决策
    }

    /**
       \brief Update counter that is used to enable/disable phase caching.
       更新用来控制phase caching的计数器，会在on和off之间反复切换，切换的频率是在参数m_fparams中控制的，在冲突归结找到冲突时调用
    */
    void context::update_phase_cache_counter() {
        m_phase_counter++;
        if (m_phase_cache_on) {
            if (m_phase_counter >= m_fparams.m_phase_caching_on) {
                m_phase_counter  = 0;
                m_phase_cache_on = false;
                if (m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE2)
                    m_phase_default = !m_phase_default;
            }
        }
        else {
            if (m_phase_counter >= m_fparams.m_phase_caching_off) {
                m_phase_counter  = 0;
                m_phase_cache_on = true;
                if (m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE2)
                    m_phase_default = !m_phase_default;
            }
        }
    }

    /**
       \brief Create an internal backtracking point
       创造中间回退点,在push，decide,decide_clasue，init_assumption中调用
    */
    void context::push_scope() {

        if (m.has_trace_stream() && !m_is_auxiliary)
            m.trace_stream() << "[push] " << m_scope_lvl << "\n";

        m_scope_lvl++;
        m_region.push_scope();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        // TRACE("context", tout << "push " << m_scope_lvl << "\n";);

        m_relevancy_propagator->push();
        s.m_assigned_literals_lim    = m_assigned_literals.size();
        s.m_trail_stack_lim          = m_trail_stack.size();
        s.m_aux_clauses_lim          = m_aux_clauses.size();
        s.m_justifications_lim       = m_justifications.size();
        s.m_units_to_reassert_lim    = m_units_to_reassert.size();

        m_qmanager->push();

        m_fingerprints.push_scope();
        m_case_split_queue->push_scope();
        m_asserted_formulas.push_scope();

        for (theory* t : m_theory_set) 
            t->push_scope_eh();
        CASSERT("context", check_invariant());
    }

    /**
       \brief Execute generic undo-objects.执行泛化的消除对象操作
    */
    void context::undo_trail_stack(unsigned old_size) {
        ::undo_trail_stack(*this, m_trail_stack, old_size);
    }

    /**
       \brief Remove watch literal idx from the given clause.
        将watch文字从给定子句中消除，此处的idx必须是0或者1
       \pre idx must be 0 or 1.
    */
    void context::remove_watch_literal(clause * cls, unsigned idx) {
        m_watches[(~cls->get_literal(idx)).index()].remove_clause(cls);
    }

    /**
       \brief Remove boolean variable from watch lists.将布尔变量从watch list中移除,无调用
    */
    void context::remove_watch(bool_var v) {
        literal lit(v);
        m_watches[lit.index()].reset();
        m_watches[(~lit).index()].reset();
    }

    /**
       \brief Remove clause，删除子句的occ，该方法会在del_clause中被调用
    */

    void context::remove_cls_occs(clause * cls) {
        remove_watch_literal(cls, 0);
        remove_watch_literal(cls, 1);
        remove_lit_occs(*cls, get_num_bool_vars());
    }

    /**
       \brief Update occurrence count of literals 更新文字的出现次数
    */
   //对于子句cls中的每个文字添加occ，在reinit_clause中被调用
    void context::add_lit_occs(clause const& cls) {
        if (!track_occs()) return;
        for (literal l : cls) {
            inc_ref(l);
        }
    }
    //对于子句中的每个小于nbv的文字，减少occ，在remove_cls_occ，reinit_clause和del_clause中被调用
    void context::remove_lit_occs(clause const& cls, unsigned nbv) {
        if (!track_occs()) return;
        for (literal l : cls) {
            if (l.var() < static_cast<int>(nbv)) 
                dec_ref(l);
        }
    }

    // TBD: enable as assertion when ready to re-check 当准备好重新检测时 作为断言启用
    void context::dec_ref(literal l) { if (track_occs() && m_lit_occs[l.index()] > 0) m_lit_occs[l.index()]--; }
    //增加l的变量对应的m_lit_occs
    void context::inc_ref(literal l) { if (track_occs()) m_lit_occs[l.index()]++; }

    /**
       \brief Delete the given clause.
        删除一个指定的子句，该子句不能在reinit栈中
       \pre Clause is not in the reinit stack.
    */
    void context::del_clause(bool log, clause * cls) {
        SASSERT(m_flushing || !cls->in_reinit_stack());
        if (log) 
            m_clause_proof.del(*cls);
        CTRACE("context", !m_flushing, display_clause_smt2(tout << "deleting ", *cls) << "\n";);
        if (!cls->deleted())
            remove_cls_occs(cls);
        cls->deallocate(m);
        m_stats.m_num_del_clause++;
    }

    /**
       \brief Delete the clauses in v at locations [old_size .. v.size())
       Reduce the size of v to old_size.
       删除old_size之后的在clause列表v中的所有子句,在pop_scope_core和flush中调用
    */
    void context::del_clauses(clause_vector & v, unsigned old_size) {
        unsigned num_collect = v.size() - old_size;
        if (num_collect == 0)
            return;
        
        clause_vector::iterator begin = v.begin() + old_size;
        clause_vector::iterator it    = v.end();
        if (num_collect > 1000) {//根据要删除的子句数量来定，如果要删除的数量较多
            uint_set watches;
            while (it != begin) {
                --it;
                clause* c = *it;
                remove_lit_occs(*c, get_num_bool_vars());
                if (!c->deleted()) {
                    c->mark_as_deleted(m);                    
                }
                watches.insert((~c->get_literal(0)).index());
                watches.insert((~c->get_literal(1)).index());
            }
            for (auto w: watches) {
                m_watches[w].remove_deleted();
            }
            for (it = v.end(); it != begin; ) {
                --it;
                (*it)->deallocate(m);
            }
            m_stats.m_num_del_clause += (v.size() - old_size);
        }
        else {//如果要删除的子句数量较少，就直接一个一个地删除
            while (it != begin) {
                --it;
                del_clause(false, *it);
            }
        }
        v.shrink(old_size);
    }


    /**
       \brief Undo variable assignments.
       取消一系列变量的赋值，直到删除到old_lim号，在pop_scope_core中被调用
    */
    void context::unassign_vars(unsigned old_lim) {
        SASSERT(old_lim <= m_assigned_literals.size());

        unsigned i = m_assigned_literals.size();//i是已经赋值的文字数
        while (i != old_lim) {//删除i到old_lim个
            --i;
            literal l                  = m_assigned_literals[i];//l是第i个待删除的文字
            CTRACE("assign_core", l.var() == 13, tout << "unassign " << l << "\n";);
            m_assignment[l.index()]    = l_undef;//设置l和l的非都是undef
            m_assignment[(~l).index()] = l_undef;
            bool_var v                 = l.var();
            bool_var_data & d          = get_bdata(v);//找到v对应的变量数据
            d.set_null_justification();//设置v对应的变量数据的证明为空
            m_case_split_queue->unassign_var_eh(v);//将v加入到case_split队列中
        }

        m_assigned_literals.shrink(old_lim);//赋值变量的文字vector缩减到old_lim
        m_qhead = old_lim;//队列头指向old_lim
        SASSERT(m_qhead == m_assigned_literals.size());
    }

    /**
       \brief Invoke method del_eh for the justification that will be deleted.
       If the method in_region() returns false, then delete operator is invoked.
       为将要被删除的justification调用del_eh方法，如果in_regin方法返回false，则删除操作会被调用， 在pop_scope_core和flush中被调用
    */
    void context::del_justifications(ptr_vector<justification> & justifications, unsigned old_lim) {
        SASSERT(old_lim <= justifications.size());
        unsigned i = justifications.size();
        while (i != old_lim) {
            --i;
            justification * js = justifications[i];
            js->del_eh(m);//调用del_eh句柄，释放由该对象占用的资源
            if (!js->in_region()) {//如果该justification不在域内，则直接回收相应的内存
                dealloc(js);
            }
            else {
                // If the justification is in a region, then explicitly invoke the destructor.
                // This is needed because some justification objects contains vectors.
                // The destructors of these vectors need to be invoked.
                //如果justification在域内，则调用析构函数。
                //这是必须的，因为一些justification对象包含数组，这些数组的析构函数需要被调用
                js->~justification();
            }
        }
        justifications.shrink(old_lim);
    }

    /**
       \brief Return true if all literals of c are assigned to false.
       如果子句c中所有文字都是false则返回true
    */
    bool context::is_empty_clause(clause const * c) const {
        unsigned num_lits = c->get_num_literals();
        for(unsigned i = 0; i < num_lits; i++) {
            literal l = c->get_literal(i);
            if (get_assignment(l) != l_false)
                return false;
        }
        return true;
    }

    /**
       \brief Return true if the given clause contains one and only one unassigned literal.
       如果指定子句只包含一个未赋值的文字，返回true
    */
    bool context::is_unit_clause(clause const * c) const {
        bool found        = false;
        unsigned num_lits = c->get_num_literals();
        for(unsigned i = 0; i < num_lits; i++) {
            literal l = c->get_literal(i);
            switch (get_assignment(l)) {
            case l_false:
                break; // skip
            case l_undef:
                if (found)
                    return false;
                else
                    found = true;
                break;
            case l_true:
                return false; // clause is already satisfied.
            }
        }
        return found;
    }

    /**
       \brief When a clause is reinitialized (see reinit_clauses) enodes and literals may
       need to be recreated. When an enode is recreated, I want to use the same generation
       number it had before being deleted. Otherwise the generation will be 0, and will affect
       the loop prevention heuristics used to control quantifier instantiation.
       Thus, I cache the generation number of enodes that will be deleted during backtracking
       and recreated by reinit_clauses.
       当子句被重新初始化，enodes和文字可能需要被重新构造，当enode被重新构造时，我想用它被删之前曾经用的生成号。
       否则该生成会是0，并且将影响用来控制量词实例化的环路预防启发式算法。
       因此，我缓存了将在回溯中被删除，并且将在reinit_clauses过程中重新构造的enode的生成号，（会存在m_cached_generation中）
    */
    void context::cache_generation(unsigned new_scope_lvl) {
        if (!m_clauses_to_reinit.empty()) {
            unsigned lim = m_scope_lvl;
            if (m_clauses_to_reinit.size() <= lim) {
                SASSERT(!m_clauses_to_reinit.empty());
                lim      = m_clauses_to_reinit.size() - 1;
            }
            for (unsigned i = new_scope_lvl; i <= lim; i++) {
                clause_vector & v = m_clauses_to_reinit[i];
                for (clause* cls : v) {
                    cache_generation(cls, new_scope_lvl);
                }
            }
        }
        if (!m_units_to_reassert.empty()) {//遍历units_to_reassert中的单元，从new_scope_lvl要reassert的单元开始，一直遍历到最后单元，进行cache_generation
            scope & s   = m_scopes[new_scope_lvl];
            unsigned i  = s.m_units_to_reassert_lim;
            unsigned sz = m_units_to_reassert.size();
            for (; i < sz; i++) {
                expr * unit = m_units_to_reassert.get(i);
                cache_generation(unit, new_scope_lvl);
            }
        }
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::cache_generation(clause const * cls, unsigned new_scope_lvl) {
        cache_generation(cls->get_num_literals(), cls->begin(), new_scope_lvl);
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::cache_generation(unsigned num_lits, literal const * lits, unsigned new_scope_lvl) {
        for(unsigned i = 0; i < num_lits; i++) {
            bool_var v          = lits[i].var();
            unsigned ilvl       = get_intern_level(v);
            if (ilvl > new_scope_lvl)
                cache_generation(bool_var2expr(v), new_scope_lvl);
        }
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::cache_generation(expr * n, unsigned new_scope_lvl) {
        ptr_buffer<expr> todo;
        todo.push_back(n);
        while (!todo.empty()) {
            expr * n = todo.back();
            todo.pop_back();
            if (m_cache_generation_visited.contains(n))
                continue;
            m_cache_generation_visited.insert(n);
            if (is_app(n)) {
                if (e_internalized(n)) {
                    enode * e     = get_enode(n);
                    unsigned ilvl = e->get_iscope_lvl();
                    if (ilvl <= new_scope_lvl)
                        continue; // node and its children will not be recreated during backtracking
                    TRACE("cached_generation", tout << "caching: #" << n->get_id() << " " << e->get_generation() << "\n";);
                    m_cached_generation.insert(n, e->get_generation());
                }
                for (expr * arg : *to_app(n)) {
                    if (is_app(arg) || is_quantifier(arg))
                        todo.push_back(arg);
                }
            }
            else if (is_quantifier(n) && b_internalized(n)) {
                m_cached_generation.insert(n, m_qmanager->get_generation(to_quantifier(n)));
                todo.push_back(to_quantifier(n)->get_expr());
            }
        }
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl) 
       在resolve_confict和pop_scope_core中被调用
    */
    void context::reset_cache_generation() {
        m_cache_generation_visited.reset();
        m_cached_generation.reset();
    }

    /**
       \brief Reinitialize learned clauses (lemmas) that contain boolean variables
       that were deleted during backtracking.

       \remark num_bool_vars contains the number of boolean variables alive
       after backtracking. So, a clause contains a dead variable if it
       contains a literal l where l.var() >= num_bool_vars.
       重新初始化包含 在回退过程中被删除的布尔变量 的学习子句（lemma）在 pop_scope_core 中被调用
       num_bool_vars包含了在回退之后还存活的布尔变量的数目。因此如果一个子句包含了一个文字其变量号>num_bool_vars则该子句包含一个死变量（该子句需要被重新初始化）
    */
    void context::reinit_clauses(unsigned num_scopes, unsigned num_bool_vars) {
        TRACE("reinit_clauses_bug", display_watch_lists(tout););
        if (m_clauses_to_reinit.empty())
            return;
        unsigned lim = m_scope_lvl + num_scopes;
        if (m_clauses_to_reinit.size() <= lim) {
            SASSERT(!m_clauses_to_reinit.empty());
            lim      = m_clauses_to_reinit.size() - 1;
        }
        for (unsigned i = m_scope_lvl+1; i <= lim; i++) {
            clause_vector & v = m_clauses_to_reinit[i];
            for (clause* cls : v) {//遍历从m_scope_lvl+1后面num_scopes层的需要reinit的子句集合中的子句，逐个reinit
                if (cls->deleted()) {
                    cls->release_atoms(m);
                    cls->m_reinit              = false;
                    cls->m_reinternalize_atoms = false;
                    continue;
                }
                SASSERT(cls->in_reinit_stack());
                bool keep = false;
                if (cls->reinternalize_atoms()) {
                    SASSERT(cls->get_num_atoms() == cls->get_num_literals());
                    for (unsigned j = 0; j < 2; j++) {//考察子句cls的watch 文字
                        literal l           = cls->get_literal(j);
                        if (l.var() < static_cast<int>(num_bool_vars)) {
                            // This boolean variable was not deleted during backtracking
                            //该布尔变量在回退过程中没有被删除，则它还是一个watch 文字。因为该子句可能在重新初始化之后有新的watch文字，因此该watch被删除
                            // So, it is still a watch literal. I remove the watch, since
                            // the clause may have new watch-literals after reinitialization.
                            remove_watch_literal(cls, j);
                        }
                    }

                    unsigned num = cls->get_num_literals();

                    remove_lit_occs(*cls, num_bool_vars);

                    unsigned ilvl       = 0;
                    (void)ilvl;
                    for (unsigned j = 0; j < num; j++) {//遍历cls中的文字
                        expr * atom     = cls->get_atom(j);
                        bool   sign     = cls->get_atom_sign(j);
                        // Atom can be (NOT foo). This can happen, for example, when
                        // the NOT-application is a child of an uninterpreted function symbol.
                        // So, when reinternalizing the NOT-atom I should set the gate_ctx to false,
                        // and force expression to be reinternalized.
                        // Otherwise I set gate_ctx to true
                        bool gate_ctx = !m.is_not(atom);
                        internalize(atom, gate_ctx);
                        SASSERT(b_internalized(atom));
                        bool_var v      = get_bool_var(atom);
                        DEBUG_CODE({
                            if (get_intern_level(v) > ilvl)
                                ilvl = get_intern_level(v);
                        });
                        literal l(v, sign);
                        cls->set_literal(j, l);
                    }
                    SASSERT(ilvl <= m_scope_lvl);
                    int w1_idx = select_watch_lit(cls, 0);
                    cls->swap_lits(0, w1_idx);
                    int w2_idx = select_watch_lit(cls, 1);
                    cls->swap_lits(1, w2_idx);
                    add_watch_literal(cls, 0);
                    add_watch_literal(cls, 1);

                    add_lit_occs(*cls);

                    literal l1 = cls->get_literal(0);
                    literal l2 = cls->get_literal(1);

                    if (get_assignment(l1) == l_false)
                        set_conflict(b_justification(cls));//如果l1是false，说明该子句本就是全false，则是冲突
                    else if (get_assignment(l2) == l_false)//如果l1是true同时l2是false，说明该子句是单元子句，则要给l1赋值
                        assign(l1, b_justification(cls));

                    TRACE("reinit_clauses", tout << "reinit clause:\n"; display_clause_detail(tout, cls); tout << "\n";
                          tout << "activity: " << cls->get_activity() << ", num_bool_vars: " << num_bool_vars << ", scope_lvl: "
                          << m_scope_lvl << "\n";);
                    keep = true;
                }
                else {
                    SASSERT(!cls->reinternalize_atoms());
                    literal l1 = cls->get_literal(0);
                    literal l2 = cls->get_literal(1);
                    if (get_assignment(l1) == l_false && is_empty_clause(cls)) {
                        set_conflict(b_justification(cls));
                        keep = true;
                    }
                    else if (get_assignment(l2) == l_false && get_assignment(l1) == l_undef && is_unit_clause(cls)) {
                        assign(l1, b_justification(cls));
                        keep = true;
                    }
                }

                if (keep && m_scope_lvl > m_base_lvl) {
                    m_clauses_to_reinit[m_scope_lvl].push_back(cls);
                }
                else {
                    // clause do not need to be in the reinit stack anymore,
                    // because it will be deleted when the base level is
                    // backtracked.子句不需要再在reinit栈中了，因为当base level被回溯时它会被删除
                    cls->release_atoms(m);
                    cls->m_reinit              = false;
                    cls->m_reinternalize_atoms = false;
                }
            }
            v.reset();
        }
        CASSERT("reinit_clauses", check_clauses(m_lemmas));
        TRACE("reinit_clauses_bug", display_watch_lists(tout););
    }
    //在pop_scope_core中被调用，重新断言单元，从回退层的units_to_reassert_lim到最后的m_units_to_reassert中的单元子句，重新断言
    void context::reassert_units(unsigned units_to_reassert_lim) {
        unsigned i  = units_to_reassert_lim;
        unsigned sz = m_units_to_reassert.size();
        for (; i < sz; i++) {
            expr * unit   = m_units_to_reassert.get(i);
            bool gate_ctx = true;
            internalize(unit, gate_ctx);
            bool_var v    = get_bool_var(unit);
            bool sign     = m_units_to_reassert_sign[i] != 0;
            literal l(v, sign);
            assign(l, b_justification::mk_axiom());
            TRACE("reassert_units", tout << "reasserting #" << unit->get_id() << " " << sign << " @ " << m_scope_lvl << "\n";);
        }
        if (at_base_level()) {
            m_units_to_reassert.reset();
            m_units_to_reassert_sign.reset();
        }
    }

    /**
       \brief Backtrack 'num_scopes' scope levels. Return the number
       of boolean variables before reinitializing clauses. This value
       is useful because it can be used to detect which boolean variables
       were deleted.

       将m_scope层回溯num_scopes层，在重新初始化子句之前返回布尔变量的数目。该值是有用的，因为它可以用了检测哪个布尔变量被删除了,在resolve conflict和pop_scope中被调用
       该方法不会调用reset_cache_generation
       在pop完成之后会调用reinit_clauses来重新初始化子句
       \warning This method will not invoke reset_cache_generation.
       
    */
    unsigned context::pop_scope_core(unsigned num_scopes) {
        unsigned units_to_reassert_lim;

        try {
            if (m.has_trace_stream() && !m_is_auxiliary)
                m.trace_stream() << "[pop] " << num_scopes << " " << m_scope_lvl << "\n";

            // TRACE("context", tout << "backtracking: " << num_scopes << " from " << m_scope_lvl << "\n";);
            TRACE("pop_scope_detail", display(tout););
            SASSERT(num_scopes > 0);
            SASSERT(num_scopes <= m_scope_lvl);
            SASSERT(m_scopes.size() == m_scope_lvl);

            unsigned new_lvl = m_scope_lvl - num_scopes;

            cache_generation(new_lvl);//缓存将在回溯中被删除，并且将在reinit_clauses过程中重新构造的enode的生成号
            m_qmanager->pop(num_scopes);
            m_case_split_queue->pop_scope(num_scopes);

            TRACE("pop_scope", tout << "backtracking: " << num_scopes << ", new_lvl: " << new_lvl << "\n";);
            scope & s = m_scopes[new_lvl];
            TRACE("context", tout << "backtracking new_lvl: " << new_lvl << "\n";);

            units_to_reassert_lim = s.m_units_to_reassert_lim;

            if (new_lvl < m_base_lvl) {//如果new_lvl<base_lvl则说明已经退到之前的base层中
                base_scope & bs = m_base_scopes[new_lvl];
                del_clauses(m_lemmas, bs.m_lemmas_lim);
                m_simp_qhead = bs.m_simp_qhead_lim;
                if (!bs.m_inconsistent) {
                    m_conflict = null_b_justification;
                    m_not_l = null_literal;
                    m_unsat_proof = nullptr;
                }
                m_base_scopes.shrink(new_lvl);
            }
            else {
                m_conflict = null_b_justification;
                m_not_l = null_literal;
            }
            del_clauses(m_aux_clauses, s.m_aux_clauses_lim);

            m_relevancy_propagator->pop(num_scopes);

            m_fingerprints.pop_scope(num_scopes);
            unassign_vars(s.m_assigned_literals_lim);//把s层之后的所有被赋值的变量全都取消赋值
            undo_trail_stack(s.m_trail_stack_lim);

            for (theory* th : m_theory_set) 
                th->pop_scope_eh(num_scopes);

            del_justifications(m_justifications, s.m_justifications_lim);

            m_asserted_formulas.pop_scope(num_scopes);

            CTRACE("propagate_atoms", !m_atom_propagation_queue.empty(), tout << m_atom_propagation_queue << "\n";);

            m_eq_propagation_queue.reset();
            m_th_eq_propagation_queue.reset();
            m_th_diseq_propagation_queue.reset();
            m_atom_propagation_queue.reset();
            m_region.pop_scope(num_scopes);
            m_scopes.shrink(new_lvl);
            m_conflict_resolution->reset();

            m_scope_lvl = new_lvl;//把scope_lvl回退
            if (new_lvl < m_base_lvl) {
                m_base_lvl = new_lvl;//这是base_lv唯一赋值的地方，就是如果pop_scope后的新level比base_lvl还低
                m_search_lvl = new_lvl; // Remark: not really necessary
            }
        }
        catch (...) {
            // throwing inside pop is just not cool.
            UNREACHABLE();
            throw;
        }

        // an exception can happen when axioms are reinitialized (because they are rewritten).
        //意外可能在原子被重新初始化时出现，因为它们被重写了

        unsigned num_bool_vars = get_num_bool_vars();//num_bool_vars表示 被中间化了的布尔表达式 的数量
        // any variable >= num_bool_vars was deleted during backtracking. 任何变量>=num_bool_vars会在回退中被删除，?找不到何处会下降num_bool_vars使得变量被删除
        reinit_clauses(num_scopes, num_bool_vars);
        reassert_units(units_to_reassert_lim);
        TRACE("pop_scope_detail", tout << "end of pop_scope: \n"; display(tout););
        CASSERT("context", check_invariant());
        return num_bool_vars;
    }
    //推出num_scopes层并且重置cache，与pop_scope_core的区别在于有重置cache
    void context::pop_scope(unsigned num_scopes) {
        pop_scope_core(num_scopes);
        reset_cache_generation();
    }
    //如果当前不在base层就要回退到base层,在pop，push，check，assert_expr_core，check_preamble中调用
    void context::pop_to_base_lvl() {
        SASSERT(m_scope_lvl >= m_base_lvl);
        if (!at_base_level()) {
            unsigned num_lvls = m_scope_lvl - m_base_lvl;
            pop_scope(num_lvls);
        }
        SASSERT(m_scope_lvl == m_base_lvl);
    }
    //将m_scope_lvl回退到m_search_lvl，也就是去掉guess的部分，无调用
    void context::pop_to_search_lvl() {
        if (m_scope_lvl > get_search_level()) {
            pop_scope(m_scope_lvl - get_search_level());
        }
    }

    /**
       \brief Simplify the given clause using the assignment.  Return
       true if the clause was already satisfied, and false otherwise.
        使用赋值来化简给定子句，该子句是在lemma或者aux中，如果该子句已经被满足了，就返回true，否则返回false，该方法只会在base层使用，在simplify_clauses中被调用
       \remark This method should only be invoked if we are at the
       base level.
       
    */
    bool context::simplify_clause(clause& cls) {
        SASSERT(m_scope_lvl == m_base_lvl);
        unsigned s = cls.get_num_literals();//s表示该子句中的文字数量
        if (get_assignment(cls[0]) == l_true ||
            get_assignment(cls[1]) == l_true) {
            // clause is already satisfied.如果通过查看watch lit，该子句已经满足了，就直接返回true
            return true;
        }

        literal_buffer simp_lits;

        unsigned i = 2;
        unsigned j = i;
        bool is_taut = false;
        for(; i < s; i++) {
            literal l = cls[i];
            switch(get_assignment(l)) {//逐个遍历子句中的文字
            case l_false:
                if (m.proofs_enabled())
                    simp_lits.push_back(~l);//如果该文字已经是false的了，就将其放进simp_lits列表中
                dec_ref(l);//降低l的出现次数
                break;
            case l_true:
                is_taut = true;//如果已经是true，则本子句已经是true，并且要执行下面的
                // fallthrough
            case l_undef:
                if (i != j) {
                    cls.swap_lits(i, j);//把非false的往前移
                }
                j++;//j代表则非false的文字的序号
                break;
            }
        }

        if (j < s) {//如果不是所有的都是非false，即存在可以删除的false文字
            m_clause_proof.shrink(cls, j);//就把子句给缩减小到j这么大，后面已经是false的部分直接不要了
            cls.set_num_literals(j);
            SASSERT(j >= 2);
        }

        if (is_taut) {//如果已经是true就直接返回
            return true;
        }

        if (m.proofs_enabled() && !simp_lits.empty()) {//如果需要使用证明并且待删除的文字不为空，并且此时没有true的文字
            SASSERT(m_scope_lvl == m_base_lvl);
            justification * js = cls.get_justification();
            justification * new_js = nullptr;
            if (js->in_region())//
                new_js = mk_justification(unit_resolution_justification(m_region,
                                                                        js,
                                                                        simp_lits.size(),
                                                                        simp_lits.c_ptr()));
            else
                new_js = alloc(unit_resolution_justification, js, simp_lits.size(), simp_lits.c_ptr());//新的证明开辟新的region，并以js为祖先，并且将simp_lits复制到证明中
            cls.set_justification(new_js);
        }
        return false;//目前该子句中尚存未满足的文字，因此返回false
    }

    /**
       \brief Simplify the given vector of clauses starting at the given position.
       Return the number of deleted (already satisfied) clauses.
       化简给定的一个子句集合，从给定位置开始，返回删除的（已经满足的）子句数量
    */
    unsigned context::simplify_clauses(clause_vector & clauses, unsigned starting_at) {
        unsigned num_del_clauses = 0;
        clause_vector::iterator it  = clauses.begin();
        clause_vector::iterator end = clauses.end();
        it += starting_at;//it指向子句集合中starting_at的位置
        clause_vector::iterator it2 = it;//存放的是还没有被满足的子句
        for(; it != end; ++it) {//如果还没到达子句集合的末尾
            clause * cls = *it;//cls是指向的子句
            SASSERT(!cls->in_reinit_stack());//该子句应该不在reinit栈中
            
            if (cls->deleted()) {//如果该子句已经被删除了
                TRACE("simplify_clauses_bug", display_clause(tout << "deleted\n", cls) << "\n";);
                del_clause(true, cls);//删除给定子句
                num_del_clauses++;//被删除子句数量加一
            }
            else if (simplify_clause(*cls)) {//如果该子句在通过当前赋值化简之后已经是可满足的了,则要删除该子句，如果该子句是其watch文字的验证，则可以安全地用原子替代
                TRACE("simplify_clauses_bug", display_clause_smt2(tout << "simplified\n", *cls) << "\n";);
                for (unsigned idx = 0; idx < 2; idx++) {//选取前两个文字作为watch lit考察
                    literal     l0        = (*cls)[idx];
                    b_justification l0_js = get_justification(l0.var());//获取watch相应的验证l0_js
                    if (l0_js != null_b_justification &&
                        l0_js.get_kind() == b_justification::CLAUSE &&
                        l0_js.get_clause() == cls) {
                        // cls is the explanation of l0  如果cls是l0的解释
                        // it is safe to replace with axiom, we are at the base level. 则可以安全地用原子代替，目前是在最底层
                        SASSERT(m_scope_lvl == m_base_lvl);
                        bool_var v0 = l0.var();
                        if (m.proofs_enabled()) {//如果使用了证明
                            SASSERT(m_search_lvl == m_base_lvl);//确定目前是在最底层
                            literal_buffer simp_lits;
                            unsigned num_lits = cls->get_num_literals();
                            for(unsigned i = 0; i < num_lits; i++) {//将该子句中的除了idx外的后面的文字都放进sim_lits中
                                if (i != idx) {
                                    literal l = (*cls)[i];
                                    SASSERT(l != l0);
                                    simp_lits.push_back(~l);
                                }
                            }
                            justification * cls_js = cls->get_justification();
                            justification * js = nullptr;
                            if (!cls_js || cls_js->in_region()) {
                                // If cls_js is 0 or is allocated in a region, then
                                // we can allocate the new justification in a region too. 如果子句的验证不存在或者在一个域中被分配，则也可以在该域中分配新的新的验证
                                js = mk_justification(unit_resolution_justification(m_region,
                                                                                    cls_js,
                                                                                    simp_lits.size(),
                                                                                    simp_lits.c_ptr()));
                            }
                            else {
                                js = alloc(unit_resolution_justification, cls_js, simp_lits.size(), simp_lits.c_ptr());
                                // js took ownership of the justification object. js取的了对justification对象的所有权
                                cls->set_justification(nullptr);
                                m_justifications.push_back(js);
                            }
                            set_justification(v0, m_bdata[v0], b_justification(js));
                        }
                        else
                            m_bdata[v0].set_axiom();//如果不使用证明，就为l0位置的变量的验证设置为原子
                    }
                }
                del_clause(true, cls);//删除已经满足了的子句
                num_del_clauses++;
            }
            else {//如果目前该子句还没有被满足
                *it2 = *it;//将未满足的子句号编到最后一个子句指针
                ++it2;
                m_simp_counter += cls->get_num_literals();//化简后的文字数量
            }
        }
        clauses.set_end(it2);//设置clauses的最后一个指针未it2
        CASSERT("simplify_clauses", check_invariant());
        return num_del_clauses;
    }

    /**
       \brief Simplify the set of clauses if possible (solver is at base level).
       化简lemma和aux子句集合，仅当在base层才化简，在bounded search和restart中被调用
    */
    void context::simplify_clauses() {
        // Remark: when assumptions are used m_scope_lvl >= m_search_lvl > m_base_lvl. Therefore, no simplification is performed.
        //如果假设不是在base层(m_scope_lvl >= m_search_lvl > m_base_lvl)，则不执行化简，化简需要在没有假设没有guess的前提下执行
        if (m_scope_lvl > m_base_lvl)
            return;

        unsigned sz = m_assigned_literals.size();
        SASSERT(m_simp_qhead <= sz);

        if (m_simp_qhead == sz || m_simp_counter > 0) {//如果再次执行simplify_clauses的开销大，则不执行
            TRACE("simplify_clauses", tout << "m_simp_qhead: " << m_simp_qhead << " m_simp_counter: " << m_simp_counter << "\n";);
            return;
        }

        if (m_aux_clauses.empty() && m_lemmas.empty()) {
            TRACE("simplify_clauses", tout << "no clauses to simplify\n";);
            return;
        }

        TRACE("simplify_clauses_detail", tout << "before:\n"; display_clauses(tout, m_lemmas););

        SASSERT(check_clauses(m_lemmas));
        SASSERT(check_clauses(m_aux_clauses));


        // m_simp_counter is used to balance the cost of simplify_clause.
        //
        // After executing simplify_clauses, the counter will contain
        // an approximation of the cost of executing simplify_clauses again.
        // That is, the number of literals that will need to be visited.
        //
        // The value of the counter is decremented each time we visit
        // a variable during propagation.
        //m_simp_counter 是用来平衡simplify_clause的开销，在执行完simplify_clauses之后，该counter会估计再次执行simplify_clauses的开销，也就是需要被访问的文字数
        //每次我们在传播时访问一个变量，这个counter的值会下降（开销下降），当simplify_clause后子句尚未满足则要加上子句文字数，也就是这个未满足子句在下一次化简中需要重新计算（开销增加）
        m_simp_counter = 0;
        // the field m_simp_qhead is used to check whether there are
        // new assigned literals at the base level.
        //m_simp_qhead 用来检测是否会有在base层的新赋值文字
        m_simp_qhead = m_assigned_literals.size();

        unsigned num_del_clauses = 0;

        SASSERT(m_scope_lvl == m_base_lvl);
        if (m_base_lvl == 0) {
            num_del_clauses += simplify_clauses(m_aux_clauses, 0);
            num_del_clauses += simplify_clauses(m_lemmas, 0);
        }
        else {//如果base_lvl不在0层
            scope & s       = m_scopes[m_base_lvl - 1];//通过m_base_lvl找到scope
            base_scope & bs = m_base_scopes[m_base_lvl - 1];
            num_del_clauses += simplify_clauses(m_aux_clauses, s.m_aux_clauses_lim);//化简子句要根据上述的scope来决定开始编号，化简来辅助子句和引理中的子句
            num_del_clauses += simplify_clauses(m_lemmas, bs.m_lemmas_lim);
        }
        m_stats.m_num_del_clauses += num_del_clauses;
        m_stats.m_num_simplifications++;
        TRACE("simp_counter", tout << "simp_counter: " << m_simp_counter << " scope_lvl: " << m_scope_lvl << "\n";);
        TRACE("simplify_clauses_detail", tout << "after:\n"; display_clauses(tout, m_lemmas););
        SASSERT(check_clauses(m_lemmas) && check_clauses(m_aux_clauses));
    }

    struct clause_lt {
        bool operator()(clause * cls1, clause * cls2) const { return cls1->get_activity() > cls2->get_activity(); }//判断是否cls1的活跃度更高
    };

    /**
       \brief Delete low activity lemmas
       删除一些低活跃度的引理,在restart和bounded search中调用，根据参数来选择使用哪种删除引理的方式,在bounded search和restart中调用
    */
    inline void context::del_inactive_lemmas() {
        if (m_fparams.m_lemma_gc_strategy == LGC_NONE)
            return;
        else if (m_fparams.m_lemma_gc_half)
            del_inactive_lemmas1();
        else
            del_inactive_lemmas2();

        m_num_conflicts_since_lemma_gc = 0;
        if (m_fparams.m_lemma_gc_strategy == LGC_GEOMETRIC)
            m_lemma_gc_threshold = static_cast<unsigned>(m_lemma_gc_threshold * m_fparams.m_lemma_gc_factor);
    }

    /**
       \brief Delete (approx.) half of low activity lemmas
       删除近乎一半的低活跃度lemma（启发式部分）
    */
    void context::del_inactive_lemmas1() {
        unsigned sz            = m_lemmas.size();
        unsigned start_at      = m_base_lvl == 0 ? 0 : m_base_scopes[m_base_lvl - 1].m_lemmas_lim;
        SASSERT(start_at <= sz);
        if (start_at + m_fparams.m_recent_lemmas_size >= sz)
            return;
        IF_VERBOSE(2, verbose_stream() << "(smt.delete-inactive-lemmas"; verbose_stream().flush(););
        SASSERT (m_fparams.m_recent_lemmas_size < sz);
        unsigned end_at        = sz - m_fparams.m_recent_lemmas_size;
        SASSERT(start_at < end_at);
        std::stable_sort(m_lemmas.begin() + start_at, m_lemmas.begin() + end_at, clause_lt());
        unsigned start_del_at  = (start_at + end_at) / 2;
        unsigned i             = start_del_at;
        unsigned j             = i;
        unsigned num_del_cls   = 0;
        TRACE("del_inactive_lemmas", tout << "sz: " << sz << ", start_at: " << start_at << ", end_at: " << end_at
              << ", start_del_at: " << start_del_at << "\n";);
        for (; i < end_at; i++) {
            clause * cls = m_lemmas[i];
            if (can_delete(cls)) {
                TRACE("del_inactive_lemmas", tout << "deleting: "; display_clause(tout, cls); tout << ", activity: " <<
                      cls->get_activity() << "\n";);
                del_clause(true, cls);
                num_del_cls++;
            }
            else {
                m_lemmas[j] = cls;
                j++;
            }
        }
        // keep recent clauses
        for (; i < sz; i++) {
            clause * cls = m_lemmas[i];
            if (cls->deleted() && can_delete(cls)) {
                del_clause(true, cls);
                num_del_cls++;
            }
            else {
                m_lemmas[j++] = cls;
            }
        }
        m_lemmas.shrink(j);
        if (m_fparams.m_clause_decay > 1) {
            // rescale activity
            for (i = start_at; i < j; i++) {
                clause * cls = m_lemmas[i];
                cls->set_activity(cls->get_activity() / m_fparams.m_clause_decay);
            }
        }
        IF_VERBOSE(2, verbose_stream() << " :num-deleted-clauses " << num_del_cls << ")" << std::endl;);
    }

    /**
       \brief More sophisticated version of del_inactive_lemmas. Here the lemmas are divided in two
       groups (old and new) based on the value of m_new_old_ratio parameter.
       A clause is deleted/retained based on its activity and relevancy. Clauses with several
       unassigned literals are considered less relevant. The threshold used for activity and relevancy
       depends on which group the clauses is in.
       更复杂版本的lemma删除，这儿lemma 根据m_new_old_ratio参数被分为两类：新和旧，一个子句基于其活跃度和相关性被删除和返回。
       带有一些未赋值文字的子句被认为是不太相关的。用于活跃度和相关性的阈值基于该子句所属的组。（启发式部分）
    */
    void context::del_inactive_lemmas2() {
        IF_VERBOSE(2, verbose_stream() << "(smt.delete-inactive-clauses "; verbose_stream().flush(););
        unsigned sz            = m_lemmas.size();
        unsigned start_at      = m_base_lvl == 0 ? 0 : m_base_scopes[m_base_lvl - 1].m_lemmas_lim;
        SASSERT(start_at <= sz);
        unsigned real_sz       = sz - start_at;
        // idx of the first learned clause considered "new"
        unsigned new_first_idx = start_at + (real_sz / m_fparams.m_new_old_ratio) * (m_fparams.m_new_old_ratio - 1);
        SASSERT(new_first_idx <= sz);
        unsigned i             = start_at;
        unsigned j             = i;
        unsigned num_del_cls   = 0;
        for (; i < sz; i++) {
            clause * cls = m_lemmas[i];
            if (can_delete(cls)) {
                if (cls->deleted()) {
                    // clause is already marked for deletion 如果该子句已经被标记要删除了
                    del_clause(true, cls);
                    num_del_cls++;
                    continue;
                }
                // A clause is deleted if it has low activity and the number of unknowns is greater than a threshold.
                // The activity threshold depends on how old the clause is.
                // 一个子句如果活跃度太低，并且unknowns文字的数量大于阈值，就会被删除
                //活跃度阈值基于该子句有多老
                unsigned act_threshold = m_fparams.m_old_clause_activity -
                    (m_fparams.m_old_clause_activity - m_fparams.m_new_clause_activity) * ((i - start_at) / real_sz);
                if (cls->get_activity() < act_threshold) {
                    unsigned rel_threshold = (i >= new_first_idx ? m_fparams.m_new_clause_relevancy : m_fparams.m_old_clause_relevancy);
                    if (more_than_k_unassigned_literals(cls, rel_threshold)) {
                        del_clause(true, cls);
                        num_del_cls++;
                        continue;
                    }
                }
            }
            m_lemmas[j] = cls;
            j++;
            cls->set_activity(static_cast<unsigned>(cls->get_activity() / m_fparams.m_inv_clause_decay));
        }
        SASSERT(j <= sz);
        m_lemmas.shrink(j);
        IF_VERBOSE(2, verbose_stream() << " :num-deleted-clauses " << num_del_cls << ")" << std::endl;);
    }

    /**
       \brief Return true if "cls" has more than (or equal to) k unassigned literals.
       逐个检测子句cls中的文字，如果有大于等于k个未赋值的文字，就返回true，在删除lemma中使用
    */
    bool context::more_than_k_unassigned_literals(clause * cls, unsigned k) {
        SASSERT(k > 0);
        for (literal l : *cls) {
            if (get_assignment(l) == l_undef) {
                k--;
                if (k == 0) {
                    return true;
                }
            }
        }
        return false;
    }


#ifdef Z3DEBUG
    /**
       \brief Return true if a symbol of the given theory was already internalized.
       如果给定理论的symbol已经被内化了就返回true
    */
    bool context::already_internalized_theory(theory * th) const {
        return already_internalized_theory_core(th, m_b_internalized_stack) || already_internalized_theory_core(th, m_e_internalized_stack);
    }

    /**
       \brief Auxiliary method for #already_internalized_theory.
    */
    bool context::already_internalized_theory_core(theory * th, expr_ref_vector const & s) const {        
        expr_mark visited;
        family_id fid = th->get_id();
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * n = s.get(i);
            if (uses_theory(n, fid, visited)) {
                return true;
            }
        }
        return false;
    }
#endif
//注册插件，参数是理论，向m_theories中注册该理论，然后向m_theory_set中添加理论，并初始化该理论，依次向th中push_scope共计m_scope_lvl层
    void context::register_plugin(theory * th) {
        if (m_theories.get_plugin(th->get_family_id()) != nullptr) {
            dealloc(th);
            return; // context already has a theory for the given family id.如果context已经有了一个对给定family id的理论，就返回，因为该理论已经被注册
        }
        TRACE("internalize", tout << this << " " << th->get_family_id() << "\n";);
        SASSERT(std::find(m_theory_set.begin(), m_theory_set.end(), th) == m_theory_set.end());
        m_theories.register_plugin(th);//就向m_theories中注册该理论
        th->init();//初始化该理论
        m_theory_set.push_back(th);//向理论集合中加入th
        {
#ifdef Z3DEBUG
            // It is unsafe to invoke push_trail from the method push_scope_eh.
            flet<bool> l(m_trail_enabled, false);
#endif
            for (unsigned i = 0; i < m_scope_lvl; ++i)//依次向th中push_scope
                th->push_scope_eh();
        }
    }
//初始化用户传播，将用户传播器注册插件
    void context::user_propagate_init(
        void*                    ctx, 
        solver::push_eh_t&       push_eh,
        solver::pop_eh_t&        pop_eh,
        solver::fresh_eh_t&      fresh_eh) {
        setup_context(m_fparams.m_auto_config);
        m_user_propagator = alloc(user_propagator, *this);
        m_user_propagator->add(ctx, push_eh, pop_eh, fresh_eh);
        for (unsigned i = m_scopes.size(); i-- > 0; ) 
            m_user_propagator->push_scope_eh();
        register_plugin(m_user_propagator);
    }
    //在propagate_bool_var_enode中被调用，使用了用户传播 并且 用户传播已经被固定 并且 用户传播对应的理论变量不为空
    bool context::watches_fixed(enode* n) const {
        return m_user_propagator && m_user_propagator->has_fixed() && n->get_th_var(m_user_propagator->get_family_id()) != null_theory_var;
    }
    //在propagate_bool_var_enode中被调用，调用m_user_propogator的new_fixed句柄
    void context::assign_fixed(enode* n, expr* val, unsigned sz, literal const* explain) {
        theory_var v = n->get_th_var(m_user_propagator->get_family_id());
        m_user_propagator->new_fixed_eh(v, val, sz, explain);
    }

    void context::push() {       
        pop_to_base_lvl();
        setup_context(false);
        bool was_consistent = !inconsistent();
        internalize_assertions(); // internalize assertions before invoking m_asserted_formulas.push_scope 在调用断言公式的push_scope之前先中间化断言
        if (!m.inc())
            throw default_exception("push canceled");
        scoped_suspend_rlimit _suspend_cancel(m.limit());
        propagate();
        if (was_consistent && inconsistent() && !m_asserted_formulas.inconsistent()) {
            // logical context became inconsistent during user PUSH 逻辑context在进行用户PUSH的时候变为不一致，则要构建proof
            VERIFY(!resolve_conflict()); // build the proof
        }
        push_scope();
        m_base_scopes.push_back(base_scope());
        base_scope & bs = m_base_scopes.back();
        bs.m_lemmas_lim = m_lemmas.size();
        bs.m_inconsistent = inconsistent();
        bs.m_simp_qhead_lim = m_simp_qhead;
        m_base_lvl++;//这是base唯一可能加1的地方
        m_search_lvl++; // Not really necessary. But, it is useful to enforce the invariant m_search_lvl >= m_base_lvl 并不必要，但是对于迫使保持m_search_lvl >= m_base_lvl 有用
        SASSERT(m_base_lvl <= m_scope_lvl);
    }
    //在base的基础上推出num_scopes层。先退回到base层，然后pop_scope(num_scopes),则已经退到之前的base中去了,无调用
    void context::pop(unsigned num_scopes) {
        SASSERT (num_scopes > 0);
        if (num_scopes > m_scope_lvl) return;
        pop_to_base_lvl();
        pop_scope(num_scopes);
    }

    /**
       \brief Free memory allocated by logical context. 释放被逻辑context分配的内存
    */
    void context::flush() {
        flet<bool> l1(m_flushing, true);
        TRACE("flush", tout << "m_scope_lvl: " << m_scope_lvl << "\n";);
        m_relevancy_propagator = nullptr;
        m_model_generator->reset();
        for (theory* t : m_theory_set) {
            t->flush_eh();//对于每个理论集合中的理论都释放相应的内存
        }
        del_clauses(m_aux_clauses, 0);//删除aux_clauses
        del_clauses(m_lemmas, 0);
        del_justifications(m_justifications, 0);
        reset_tmp_clauses();
        undo_trail_stack(0);
        m_qmanager = nullptr;
        if (m_is_diseq_tmp) {
            m_is_diseq_tmp->del_eh(m, false);
            m.dec_ref(m_is_diseq_tmp->get_owner());
            enode::del_dummy(m_is_diseq_tmp);
            m_is_diseq_tmp = nullptr;
        }
        std::for_each(m_almost_cg_tables.begin(), m_almost_cg_tables.end(), delete_proc<almost_cg_table>());
    }
    //assert表达式的核心，调用m_asserted_formulas的assert_expr函数，加入断言e到公式列表中去，在assert_expr中调用
    void context::assert_expr_core(expr * e, proof * pr) {
        if (get_cancel_flag()) return;
        SASSERT(is_well_sorted(m, e));
        TRACE("begin_assert_expr", tout << mk_pp(e, m) << " " << mk_pp(pr, m) << "\n";);
        TRACE("begin_assert_expr_ll", tout << mk_ll_pp(e, m) << "\n";);
        pop_to_base_lvl();
        if (pr == nullptr)
            m_asserted_formulas.assert_expr(e);
        else
            m_asserted_formulas.assert_expr(e, pr);
        TRACE("end_assert_expr_ll", ast_mark m; m_asserted_formulas.display_ll(tout, m););
    }

    void context::assert_expr(expr * e) {
        assert_expr(e, nullptr);
    }
    //assert一个表达式，调用assert_expr_core
    void context::assert_expr(expr * e, proof * pr) {
        timeit tt(get_verbosity_level() >= 100, "smt.simplifying");
        assert_expr_core(e, pr);
    }
    //一个trail元素用一个文字表示，在mk_case_split中被push_trail调用
    class case_split_insert_trail : public trail<context> {
        literal l;
    public:
        case_split_insert_trail(literal l):
            l(l) {
        }
        void undo(context & ctx) override {
            ctx.undo_th_case_split(l);
        }
    };
    //对lits中的每对文字(l1,l2)，添加(~l1 V ~l2)来强迫lits中最多只有一个文字为真，无调用
    void context::mk_th_case_split(unsigned num_lits, literal * lits) {
        TRACE("theory_case_split", display_literals_verbose(tout << "theory case split: ", num_lits, lits); tout << std::endl;);
        // If we don't use the theory case split heuristic, 如果不使用理论case split启发式
        // for each pair of literals (l1, l2) we add the clause (~l1 OR ~l2) 对于每对文字(l1,l2)添加(~l1 V ~l2)来强迫最多只能有一个文字被赋值为true
        // to enforce the condition that at most one literal can be assigned 'true'.
        if (!m_fparams.m_theory_case_split) {
            if (!m.proofs_enabled()) {
                for (unsigned i = 0; i < num_lits; ++i) {
                    for (unsigned j = i + 1; j < num_lits; ++j) {
                        literal l1 = lits[i];
                        literal l2 = lits[j];
                        mk_clause(~l1, ~l2, (justification*) nullptr);
                    }
                }
            }
        } else {
            literal_vector new_case_split;
            for (unsigned i = 0; i < num_lits; ++i) {
                literal l = lits[i];
                SASSERT(!m_all_th_case_split_literals.contains(l.index()));
                m_all_th_case_split_literals.insert(l.index());
                push_trail(case_split_insert_trail(l));
                new_case_split.push_back(l);
            }
            m_th_case_split_sets.push_back(new_case_split);
            push_trail(push_back_vector<context, vector<literal_vector> >(m_th_case_split_sets));
            for (unsigned i = 0; i < num_lits; ++i) {
                literal l = lits[i];
                if (!m_literal2casesplitsets.contains(l.index())) {
                    m_literal2casesplitsets.insert(l.index(), vector<literal_vector>());
                }
                m_literal2casesplitsets[l.index()].push_back(new_case_split);
            }
            TRACE("theory_case_split", tout << "tracking case split literal set { ";
                  for (unsigned i = 0; i < num_lits; ++i) {
                      tout << lits[i].index() << " ";
                  }
                  tout << "}" << std::endl;
                  );
        }
    }

    void context::add_theory_aware_branching_info(bool_var v, double priority, lbool phase) {
        m_case_split_queue->add_theory_aware_branching_info(v, priority, phase);
    }
    //取消case split，在case_split_insert_trail的undo中被调用
    void context::undo_th_case_split(literal l) {
        m_all_th_case_split_literals.remove(l.index());
        if (m_literal2casesplitsets.contains(l.index())) {
            if (!m_literal2casesplitsets[l.index()].empty()) {
                m_literal2casesplitsets[l.index()].pop_back();
            }
        }
    }
    //传播理论case_split文字，该操作不会改变m_head，对于某一类理论case，如果选中了其中了一种，则其他的都要是假，例如选中了a<1则a>2，a>3等都要为假,在propogate中被调用
    bool context::propagate_th_case_split(unsigned qhead) {
        if (m_all_th_case_split_literals.empty())//如果所有理论case split的文字集合为空，则直接返回
            return true;

        // iterate over all literals assigned since the last time this method was called,
        // not counting any literals that get assigned by this method
        // this relies on bcp() to give us its old m_qhead and therefore
        // bcp() should always be called before this method
        //迭代 自上次调用此方法以来 分配的所有文字，不算被该方法赋值的文字
        //这依赖于bcp提供了旧的m_qhead指向还未处理的已赋值变量，因此bcp要在该方法之前调用
        unsigned assigned_literal_end = m_assigned_literals.size();
        for (; qhead < assigned_literal_end; ++qhead) {//逐个迭代赋值了的文字
            literal l = m_assigned_literals[qhead];
            TRACE("theory_case_split", tout << "check literal " << l.index() << std::endl; display_literal_verbose(tout, l); tout << std::endl;);
            // check if this literal participates in any theory case split 检测该文字是否参与了理论case split
            if (!m_all_th_case_split_literals.contains(l.index())) {//如果该文字没有参与任何理论case_split，则跳过
                continue;
            }
            TRACE("theory_case_split", tout << "assigned literal " << l.index() << " is a theory case split literal" << std::endl;);
            // now find the sets of literals which contain l 现在寻找包含l的文字集合，现在该文字参与了理论case_split
            vector<literal_vector> const& case_split_sets = m_literal2casesplitsets[l.index()];
            for (vector<literal_vector>::const_iterator it = case_split_sets.begin(); it != case_split_sets.end(); ++it) {
                literal_vector case_split_set = *it;//遍历所有的文字队列case_split_set，其他的文字统统为假
                TRACE("theory_case_split", tout << "found case split set { ";
                      for(literal_vector::iterator set_it = case_split_set.begin(); set_it != case_split_set.end(); ++set_it) {
                          tout << set_it->index() << " ";
                      }
                      tout << "}" << std::endl;);
                for(literal_vector::iterator set_it = case_split_set.begin(); set_it != case_split_set.end(); ++set_it) {
                    literal l2 = *set_it;//遍历case_split_set中的每一个文字l2
                    if (l2 != l) {//如果case_split_set中的文字l2不等于l
                        b_justification js(l);
                        TRACE("theory_case_split", tout << "case split literal "; l2.display(tout, m, m_bool_var2expr.c_ptr()); tout << std::endl;);
                        if (l2 == true_literal || l2 == false_literal || l2 == null_literal) continue;//如果l2是一个true或者false（永真或永假）或者空文字，则跳过
                        assign(~l2, js);//要设置l2的非为真，如果l2已经为真，则汇报冲突，l作为非l2的验证
                        if (inconsistent()) {//发现冲突
                            TRACE("theory_case_split", tout << "conflict detected!" << std::endl;);
                            return false;
                        }
                    }
                }
            }
        }
        // if we get here without detecting a conflict, we're fine
        return true;
    }
    //如果当前的断言公式不是不一致的，消除断言的公式，在internalize_assertions中被调用
    void context::reduce_assertions() {
        if (!m_asserted_formulas.inconsistent()) {
            // SASSERT(at_base_level());
            m_asserted_formulas.reduce();//消除断言的公式
        }
    }
    //判断是否是有效的假设，假设应该是未被解释的bool变量 在validate_assumptions，internalize_proxies中被调用
    static bool is_valid_assumption(ast_manager & m, expr * a) {
        expr* arg;
        if (!m.is_bool(a))
            return false;
        if (is_uninterp_const(a))
            return true;
        if (m.is_not(a, arg) && is_uninterp_const(arg))
            return true;
        if (!is_app(a))
            return false;
        if (m.is_true(a) || m.is_false(a))
            return true;
        if (is_app(a) && to_app(a)->get_family_id() == m.get_basic_family_id())
            return false;
        if (is_app(a) && to_app(a)->get_num_args() == 0)
            return true;
        return false;
    }
    //中间化“代理”，在init_assumptions中使用
    void context::internalize_proxies(expr_ref_vector const& asms, vector<std::pair<expr*,expr_ref>>& asm2proxy) {
        for (expr* e : asms) {
            if (is_valid_assumption(m, e)) {//如果asms中的表达式是valid，将其加入到asm2proxy中
                asm2proxy.push_back(std::make_pair(e, expr_ref(e, m)));
            }
            else {//如果表达式不是valid（即不是未解释的布尔变量），先向m_asserted_formulas中加入一个imply(proxy,e)，然后将(e,proxy)加入到asm2proxy中
                expr_ref proxy(m), fml(m);
                proxy = m.mk_fresh_const("proxy", m.mk_bool_sort());
                fml = m.mk_implies(proxy, e);
                m_asserted_formulas.assert_expr(fml);
                asm2proxy.push_back(std::make_pair(e, proxy));
            }
        }
        // The new assertions are of the form 'proxy => assumption'
        // so clause simplification is sound even as these are removed after pop_scope.新的断言以“代理=>假设”的形式，所以子句化简是可靠的，即使在pop_scope之后
        internalize_assertions();
    }

    //中间化assertion,将其转换为子句，如果断言的公式是一致的，就遍历所有公式并中间化该子句
    //如果存在不一致，就要调用asserted_inconsistent来设置冲突，会在初始化assertion部分调用，构造子句
    void context::internalize_assertions() {
        if (get_cancel_flag()) return;
        TRACE("internalize_assertions", tout << "internalize_assertions()...\n";);
        timeit tt(get_verbosity_level() >= 100, "smt.preprocessing");
        reduce_assertions();
        if (get_cancel_flag()) return;
        if (!m_asserted_formulas.inconsistent()) {//如果断言的公式不是不一致的
            unsigned sz    = m_asserted_formulas.get_num_formulas();//sz是公式数量
            unsigned qhead = m_asserted_formulas.get_qhead();//qhead指向公式的第一个
            // std::cout<<sz-qhead<<"\n";
            while (qhead < sz) {//遍历所有公式
                if (get_cancel_flag()) {
                    m_asserted_formulas.commit(qhead);
                    return;
                }
                expr * f   = m_asserted_formulas.get_formula(qhead);//获得位列qhead号的公式,是一个表达式
                proof * pr = m_asserted_formulas.get_formula_proof(qhead);//获得位列qhead号的证明
                SASSERT(!pr || f == m.get_fact(pr));
                internalize_assertion(f, pr, 0);//中间化该子句
                qhead++;
            }
            m_asserted_formulas.commit();
        }
        if (m_asserted_formulas.inconsistent() && !inconsistent()) {
            asserted_inconsistent();//如果存在不一致，就要调用asserted_inconsistent来设置冲突
        }
        TRACE("internalize_assertions", tout << "after internalize_assertions()...\n";
              tout << "inconsistent: " << inconsistent() << "\n";);
        TRACE("after_internalize_assertions", display(tout););
    }
    //断言不一致时进行的操作，先获取断言的公式的不一致证明作为unsat证明，然后设置冲突,在search和internalize_assertions中被调用
    void context::asserted_inconsistent() {
        proof * pr = m_asserted_formulas.get_inconsistency_proof();
        m_unsat_proof = pr;
        if (!pr) {
            set_conflict(b_justification::mk_axiom());
        }
        else {
            set_conflict(mk_justification(justification_proof_wrapper(*this, pr)));
        }
    }

    /**
       \brief Assumptions must be uninterpreted boolean constants (aka propositional variables).
       假设必须是未解释的布尔常数，（也就是命题变量），如果有不是的就返回false,在check中被调用
       遍历asm中的各个假设，如果其中有个不是valid就返回false
    */
    bool context::validate_assumptions(expr_ref_vector const& asms) {
        for (expr* a : asms) {
            SASSERT(a);
            if (!is_valid_assumption(m, a)) {//遍历expr_ref_vector中的各个expr，如果有一个不满足是valid假设就返回，并警告：一个假设一定要是个命题变量
                warning_msg("an assumption must be a propositional variable or the negation of one");
                return false;
            }
        }
        return true;
    }
    //初始化子句，在check()中被调用
    void context::init_clause(expr_ref_vector const& _clause) {
        literal_vector lits;
        for (expr* lit : _clause) {//遍历子句中的文字
            internalize_formula(lit, true);//internalize各个文字
            mark_as_relevant(lit);//将该文字标记为相关
            lits.push_back(get_literal(lit));//在lits的列表中加入该文字
        }
        clause* clausep = nullptr;
        if (lits.size() >= 2) {//如果该子句中的文字数量大于等于2
            justification* js = nullptr;
            if (m.proofs_enabled()) {//如果需要证明
                proof * pr = mk_clause_def_axiom(lits.size(), lits.c_ptr(), nullptr);//设置一个证明pr
                js = mk_justification(justification_proof_wrapper(*this, pr));//将这个证明作为一个验证js
            }
            clausep = clause::mk(m, lits.size(), lits.c_ptr(), CLS_AUX, js);//根据js和文字列表产生一个新的子句?
        }
        m_tmp_clauses.push_back(std::make_pair(clausep, lits));//将该子句放入暂时子句列表中？暂时子句（其中存放着子句指针clausesep和文字列表的pair）
    }
    //重制tmp_clause列表，如果tmp_clause中的子句指针存在，就删除指定的子句
    void context::reset_tmp_clauses() {
        for (auto& p : m_tmp_clauses) {
            if (p.first) del_clause(false, p.first);//如果tmp_clause中的子句指针存在，那就删除指定的子句
        }
        m_tmp_clauses.reset();
    }

    //决策子句 在decide中被调用
    //会变量tmp_clauses中的所有子句
    //如果所有子句都已经被满足了，就返回l_true
    //如果存在一个子句已经为false：第一个文字就是false，就返回false，并且设置冲突
    //如果在某个子句中存在未赋值变量就对其赋值，返回l_undef
    lbool context::decide_clause() {
        if (m_tmp_clauses.empty()) return l_true;//如果没有tmp_clause，就返回true
        for (auto & tmp_clause : m_tmp_clauses) {//对于tmp_clause中的每个子句tmp_clause
            literal_vector& lits = tmp_clause.second;//找到对应的文字列表lits
            literal unassigned = null_literal;
            for (literal l : lits) {
                switch (get_assignment(l)) {//逐个验证lits中的文字l
                case l_false:
                    break;//如果找到了一个false的文字，就停止遍历lits
                case l_true:
                    goto next_clause;//如果该子句已经sat了，则考察下一个子句
                default:
                    unassigned = l;//找到了一个未赋值的文字
                }         
            }

            if (unassigned != null_literal) {//如果存在未赋值的文字（在第一个false文字之前出现过undef），说明可以赋值，返回undef
                shuffle(lits.size(), lits.c_ptr(), m_random);//随机重排lits
                push_scope();
                assign(unassigned, b_justification::mk_axiom(), true);//对该未赋值文字赋值未真
                return l_undef;
            }
            //如果在第一个false文字之前没有出现过undef，即第一个就是false（若是watch lit的方式说明该子句为false）
            if (lits.size() == 1) {//如果只有该子句只有一个文字，说明这个文字不能被赋值为false，也就是冲突的原因
                set_conflict(b_justification(), ~lits[0]);
            }
            else {
                set_conflict(b_justification(tmp_clause.first), null_literal);
            }
            VERIFY(!resolve_conflict());
            return l_false;//说明该子句已经为false，产生了冲突
        next_clause:
            ;
        }
        return l_true;
    }
    //初始化假设，在check()中被调用
    void context::init_assumptions(expr_ref_vector const& asms) {
        reset_assumptions();
        m_literal2assumption.reset();
        m_unsat_core.reset();
        if (!asms.empty()) {
            // We must give a chance to the theories to propagate before we create a new scope...
            //必须要先进行理论传播再构造一个新scope
            propagate();
            // Internal backtracking scopes (created with push_scope()) must only be created when we are 内部回溯层（随着push_scope()创造的）必须仅在一致状态下被创造
            // in a consistent context.
            if (inconsistent())
                return;
            if (get_cancel_flag())
                return;
            push_scope();
            vector<std::pair<expr*,expr_ref>> asm2proxy;
            internalize_proxies(asms, asm2proxy);//将假设转为代理：asm2proxy
            for (auto const& p: asm2proxy) {//逐个遍历这些假设
                if (inconsistent())
                    break;
                expr_ref curr_assumption = p.second;//当前假设
                expr* orig_assumption = p.first;//原假设
                if (m.is_true(curr_assumption)) continue;//如果当前假设已经是true了，则跳过
                SASSERT(is_valid_assumption(m, curr_assumption));//当前假设是一个valid的假设
                proof * pr = m.mk_asserted(curr_assumption);
                internalize_assertion(curr_assumption, pr, 0);//中间化断言 当前假设
                literal l = get_literal(curr_assumption);//获取当前假设对应的文字
                SASSERT(get_assignment(l) != l_undef);
                SASSERT(l != false_literal || inconsistent());//l==false_literal-->inconsistent
                if (l == true_literal || l == false_literal) {//如果当前假设对应的文字是true或者false，则跳过
                    continue;
                }
                m_literal2assumption.insert(l.index(), orig_assumption);
                m_assumptions.push_back(l);//把当前假设对应的文字l 加入assumption中
                get_bdata(l.var()).m_assumption = true;//设置当前假设对应的文字 是一个assumption                
                SASSERT(is_relevant(l));
                TRACE("assumptions", tout << l << ":" << curr_assumption << " " << mk_pp(orig_assumption, m) << "\n";);
            }
        }
        m_search_lvl = m_scope_lvl;//将scope赋给search
        SASSERT(asms.empty() || m_search_lvl > m_base_lvl);//没有假设-->search_lvl>base_lvl
        SASSERT(!asms.empty() || m_search_lvl == m_base_lvl);
        TRACE("after_internalization", display(tout););
    }
    //重制假设，对于假设中的每个文字lit，将其对应的变量的assumption设为false,并且重置m_assumption
    void context::reset_assumptions() {
        TRACE("unsat_core_bug", tout << "reset " << m_assumptions << "\n";);
        for (literal lit : m_assumptions) 
            get_bdata(lit.var()).m_assumption = false;
        m_assumptions.reset();
    }
    //判断是否需要重新搜索，如果r不是l_false或者unsat_core是空的就不需要（即如果r是l_undf或者l_true就返回false了，不再重新搜索），如果r是l_false并且存在一个理论需要重新搜索就需要
    bool context::should_research(lbool r) {
        if (r != l_false || m_unsat_core.empty()) { 
            return false;
        }
        for (theory* th : m_theory_set) {
            if (th->should_research(m_unsat_core)) {
                return true;
            }
        }
        return false;
    }
    //构造一个unsat_core (目前不使用)
    lbool context::mk_unsat_core(lbool r) {        
        if (r != l_false) return r;
        SASSERT(inconsistent());
        if (!tracking_assumptions()) {
            SASSERT(m_assumptions.empty());
            return l_false;
        }
        uint_set already_found_assumptions;
        literal_vector::const_iterator it  = m_conflict_resolution->begin_unsat_core();
        literal_vector::const_iterator end = m_conflict_resolution->end_unsat_core();
        for (; it != end; ++it) {
            literal l = *it;
            TRACE("unsat_core_bug", tout << "answer literal: " << l << "\n";);
            SASSERT(get_bdata(l.var()).m_assumption);
            if (!m_literal2assumption.contains(l.index())) l.neg();
            SASSERT(m_literal2assumption.contains(l.index()));
            if (!already_found_assumptions.contains(l.index())) {
                already_found_assumptions.insert(l.index());
                expr* orig_assumption = m_literal2assumption[l.index()];
                m_unsat_core.push_back(orig_assumption);
                TRACE("assumptions", tout << l << ": " << mk_pp(orig_assumption, m) << "\n";);
            }
        }
        reset_assumptions();
        pop_to_base_lvl(); // undo the push_scope() performed by init_assumptions 取消由init_assumption执行的push_scope操作
        m_search_lvl = m_base_lvl;
        std::sort(m_unsat_core.c_ptr(), m_unsat_core.c_ptr() + m_unsat_core.size(), ast_lt_proc());
        TRACE("unsat_core_bug", tout << "unsat core:\n" << m_unsat_core << "\n";);
        validate_unsat_core();
        // theory validation of unsat core
        for (theory* th : m_theory_set) {
            lbool theory_result = th->validate_unsat_core(m_unsat_core);
            if (theory_result == l_undef) {
                return l_undef;
            }
        }
        return l_false;
    }

    /**
       \brief Make some checks before starting the search.
       Return true if succeeded.
       在开始搜索之前进行一些检测，如果检测成功返回true
    */
    bool context::check_preamble(bool reset_cancel) {
        if (m.has_trace_stream() && !m_is_auxiliary)
            m.trace_stream() << "[begin-check] " << m_scope_lvl << "\n";

        if (memory::above_high_watermark()) {
            m_last_search_failure = MEMOUT;
            return false;
        }
        reset_tmp_clauses();
        m_unsat_core.reset();
        m_stats.m_num_checks++;
        pop_to_base_lvl();      
        m_conflict_resolution->reset();
        return true;
    }

    /**
       \brief Execute some finalization code after performing the search.
       在执行完搜索之后执行的一些终结代码
    */
    lbool context::check_finalize(lbool r) {
        TRACE("after_search", display(tout << "result: " << r << "\n");
              m_case_split_queue->display(tout << "case splits\n");
              );
        display_profile(verbose_stream());
        if (r == l_true && get_cancel_flag()) {
            r = l_undef;
        }
        if (r == l_true && gparams::get_value("model_validate") == "true") {
            recfun::util u(m);
            model_ref mdl;
            get_model(mdl);//获取求解后的model，对每个理论逐个遍历验证模型的valid            
            if (u.get_rec_funs().empty()) {
                if (mdl.get()) {
                    for (theory* t : m_theory_set) {
                        t->validate_model(*mdl);
                    }
                }
            }
#if 0
            for (literal lit : m_assigned_literals) {
                if (!is_relevant(lit)) continue;
                expr* v = m_bool_var2expr[lit.var()];
                if (lit.sign() ? m_model->is_true(v) : m_model->is_false(v)) {
                    IF_VERBOSE(10, verbose_stream() 
                               << "invalid assignment " << (lit.sign() ? "true" : "false") 
                               << " to #" << v->get_id() << " := " << mk_bounded_pp(v, m, 3) << "\n");
                }
            }
            for (clause* cls : m_aux_clauses) {
                bool found = false;
                IF_VERBOSE(10, display_clause_smt2(verbose_stream() << "check:\n", *cls) << "\n");                    
                for (literal lit : *cls) {
                    expr* v = m_bool_var2expr[lit.var()];
                    if (lit.sign() ? !m_model->is_true(v) : !m_model->is_false(v)) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    IF_VERBOSE(10, display_clause_smt2(verbose_stream() << "not satisfied:\n", *cls) << "\n");                    
                }
            }
            for (clause* cls : m_lemmas) {
                bool found = false;
                IF_VERBOSE(10, display_clause_smt2(verbose_stream() << "check:\n", *cls) << "\n");                    
                for (literal lit : *cls) {
                    expr* v = m_bool_var2expr[lit.var()];
                    if (lit.sign() ? !m_model->is_true(v) : !m_model->is_false(v)) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    IF_VERBOSE(10, display_clause_smt2(verbose_stream() << "not satisfied:\n", *cls) << "\n");                    
                }
            }

            unsigned l_idx = 0;
            for (watch_list const& wl : m_watches) {
                literal l1 = to_literal(l_idx++);
                literal neg_l1 = ~l1;
                expr* v = m_bool_var2expr[l1.var()];
                if (neg_l1.sign() ? !m_model->is_true(v) : !m_model->is_false(v)) {
                    continue;
                }
                literal const * it2  = wl.begin_literals();
                literal const * end2 = wl.end_literals();
                for (; it2 != end2; ++it2) {
                    literal l2 = *it2;
                    if (l1.index() >= l2.index()) {
                        continue;
                    }
                    literal lits[2] = { neg_l1, l2 };
                    IF_VERBOSE(10, display_literals_smt2(verbose_stream() << "check: ", 2, lits) << "\n";);
                    v = m_bool_var2expr[l2.var()];
                    if (l2.sign() ? !m_model->is_true(v) : !m_model->is_false(v)) {
                        continue;
                    }
                    IF_VERBOSE(10, display_literals_smt2(verbose_stream() << "not satisfied: ", 2, lits) << "\n";);
                }
            }
#endif
        }
        return r;
    }

    /**
       \brief Setup the logical context based on the current set of
       asserted formulas and execute the check command.

       \remark A logical context can only be configured at scope level 0,
       and before internalizing any formulas.
       基于当前的已断言的公式来设置逻辑context，并且执行check命令
       逻辑context只能在scope 0级 并且 在internalizing任何公式之前 才能被配置
       此处是入口函数!!
    */
    lbool context::setup_and_check(bool reset_cancel) {
        // std::cout<<"begin search context\n";
        if (!check_preamble(reset_cancel)) return l_undef;
        SASSERT(m_scope_lvl == 0);
        SASSERT(!m_setup.already_configured());
        setup_context(m_fparams.m_auto_config);

        if (m_fparams.m_threads > 1 && !m.has_trace_stream()) {
            parallel p(*this);
            expr_ref_vector asms(m);
            return p(asms);
        }

        internalize_assertions();//此处中间化断言，形成子句,此处加入到clauses_vec中
        expr_ref_vector theory_assumptions(m);
        add_theory_assumptions(theory_assumptions);
        if (!theory_assumptions.empty()) {//理论assumption不为空
            TRACE("search", tout << "Adding theory assumptions to context" << std::endl;);
            return check(0, nullptr, reset_cancel);
        }
        else {//如果理论assumption为空,例子会进入此处
            TRACE("before_search", display(tout););
            // display_expr_bool_var_map(std::cout);//在搜索开始之前打印bool变量和表达式的对应关系,在此处将布尔抽象后的文字与文字编号对应起来，即调用了build_lits
            expr_bool_var_map();
            // display_assignment(std::cout);//在搜索开始之前先获取已经单元传播赋值的部分bool变量
            m_ls_solver->build_instance(clauses_vec);
#ifdef IDL_DEBUG
            std::cout<<"0\n"<<clauses_vec.size()<<"\n";
            for(auto cl:clauses_vec){
                std::cout<<"(";
                for(auto l:cl){std::cout<<" "<<l;}
                std::cout<<" )\n";
            }
                std::cout<<"after builid instance\n";
                std::cout<<"clause num:"<<m_ls_solver->_num_clauses<<"\n"<<"bool var num:"<<m_ls_solver->_num_bool_vars<<"\n";
                // m_ls_solver->print_formula();
#endif
            // m_ls_solver->local_search();
            // if(m_ls_solver->_best_found_hard_cost==0){std::cout<<"local search sat\n"<<m_timer.get_seconds()<<"\n";return l_true;}
            return check_finalize(search());
        }
    }
    //根据参数use_static_features来返回不同的config模式
    config_mode context::get_config_mode(bool use_static_features) const {
        if (!m_fparams.m_auto_config)
            return CFG_BASIC;
        if (use_static_features)
            return CFG_AUTO;
        return CFG_LOGIC;
    }
    //设置context，参数是是否是否使用静态特征，
    void context::setup_context(bool use_static_features) {
        if (m_setup.already_configured() || inconsistent()) {//如果已经设置了m_setup的设定，则设定relevancy_lvl如下
            m_relevancy_lvl = std::min(m_fparams.m_relevancy_lvl, m_relevancy_lvl);
            return;
        }
        m_setup(get_config_mode(use_static_features));
        m_relevancy_lvl = m_fparams.m_relevancy_lvl;
        setup_components();
    }

    void context::setup_components() {
        m_asserted_formulas.setup();
        m_random.set_seed(m_fparams.m_random_seed);
        m_dyn_ack_manager.setup();
        m_conflict_resolution->setup();

        if (!relevancy())
            m_fparams.m_relevancy_lemma = false;

        // setup all the theories 设置所有的理论
        for (theory* th : m_theory_set) 
            th->setup();
    }
    //添加一系列的理论假设，逐个遍历理论集合中的理论，向其中加入理论assumption，在check中被调用
    void context::add_theory_assumptions(expr_ref_vector & theory_assumptions) {
        for (theory* th : m_theory_set) {
            th->add_theory_assumptions(theory_assumptions);
        }
    }
    //check的重载，加入并行处理
    lbool context::check(unsigned num_assumptions, expr * const * assumptions, bool reset_cancel) {
        if (!check_preamble(reset_cancel)) return l_undef;
        SASSERT(at_base_level());
        setup_context(false);
        if (m_fparams.m_threads > 1 && !m.has_trace_stream()) {            
            expr_ref_vector asms(m, num_assumptions, assumptions);
            parallel p(*this);//并行
            return p(asms);
        }
        lbool r;
        do {
            pop_to_base_lvl();
            expr_ref_vector asms(m, num_assumptions, assumptions);
            internalize_assertions();
            add_theory_assumptions(asms);                
            TRACE("unsat_core_bug", tout << asms << "\n";);        
            init_assumptions(asms);
            TRACE("before_search", display(tout););
            r = search();
            r = mk_unsat_core(r);        
        }
        while (should_research(r));
        r = check_finalize(r);
        return r;
    }
    //入口函数，调用search检测
    lbool context::check(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) {
        if (!check_preamble(true)) return l_undef;
        TRACE("before_search", display(tout););
        setup_context(false);
        lbool r;
        do {
            pop_to_base_lvl();//回退到base层
            expr_ref_vector asms(cube);
            internalize_assertions();
            add_theory_assumptions(asms);//添加一系列的cube中的理论假设
            // introducing proxies: if (!validate_assumptions(asms)) return l_undef; 引入代理：如果clauses子句集中的子句不是valid，则返回undef
            for (auto const& clause : clauses) if (!validate_assumptions(clause)) return l_undef;
            init_assumptions(asms);//初始化assumption
            for (auto const& clause : clauses) init_clause(clause);//对于每个子句逐个初始化
            r = search();  //进行搜索 
            r = mk_unsat_core(r);             
        }
        while (should_research(r));
        r = check_finalize(r);
        return r;           
    }
    //初始化搜索，初始化一系列的参数，可以在此处调整参数设置!!!
    void context::init_search() {
        for (theory* th : m_theory_set) {
            th->init_search_eh();
        }
        m_qmanager->init_search_eh();
        m_incomplete_theories.reset();
        m_num_conflicts                = 0;
        m_num_conflicts_since_restart  = 0;
        m_num_conflicts_since_lemma_gc = 0;
        m_num_restarts                 = 0;
        m_restart_threshold            = m_fparams.m_restart_initial;
        m_restart_outer_threshold      = m_fparams.m_restart_initial;
        m_agility                      = 0.0;
        m_luby_idx                     = 1;
        m_lemma_gc_threshold           = m_fparams.m_lemma_gc_initial;
        m_last_search_failure          = OK;
        m_unsat_proof                  = nullptr;
        m_unsat_core                   .reset();
        m_dyn_ack_manager              .init_search_eh();
        m_final_check_idx              = 0;
        m_phase_default                = false;
        m_case_split_queue             ->init_search_eh();
        m_next_progress_sample         = 0;
        TRACE("literal_occ", display_literal_num_occs(tout););
    }
    //结束搜索，调用case_split_queue的end_search_eh句柄，在search中被调用
    void context::end_search() {
        m_case_split_queue->end_search_eh();
    }
    //该方法在restart中被调用，根据重启策略调整增加重启阈值
    void context::inc_limits() {
        if (m_num_conflicts_since_restart >= m_restart_threshold) {
            switch (m_fparams.m_restart_strategy) {
            case RS_GEOMETRIC:
                m_restart_threshold = static_cast<unsigned>(m_restart_threshold * m_fparams.m_restart_factor);
                break;
            case RS_IN_OUT_GEOMETRIC:
                m_restart_threshold = static_cast<unsigned>(m_restart_threshold * m_fparams.m_restart_factor);
                if (m_restart_threshold > m_restart_outer_threshold) {
                    m_restart_threshold = m_fparams.m_restart_initial;
                    m_restart_outer_threshold = static_cast<unsigned>(m_restart_outer_threshold * m_fparams.m_restart_factor);
                }
                break;
            case RS_LUBY:
                m_luby_idx ++;
                m_restart_threshold = static_cast<unsigned>(get_luby(m_luby_idx) * m_fparams.m_restart_initial);
                break;
            case RS_FIXED:
                break;
            case RS_ARITHMETIC:
                m_restart_threshold = static_cast<unsigned>(m_restart_threshold + m_fparams.m_restart_factor);
                break;
            default:
                break;
            }
        }
        m_num_conflicts_since_restart = 0;
    }

    //搜索过程，调用核心部分bounded_search
    lbool context::search() {
        if (m_asserted_formulas.inconsistent()) {
            asserted_inconsistent();//如果断言的公式已经是不一致的了，直接返回l_false，先获取断言的公式的不一致证明作为unsat证明，然后设置冲突
            return l_false;
        }
        if (inconsistent()) {//如果已经不一致
            VERIFY(!resolve_conflict());
            return l_false;
        }
        if (get_cancel_flag())
            return l_undef;
        timeit tt(get_verbosity_level() >= 100, "smt.stats");
        reset_model();
        SASSERT(at_search_level());
        TRACE("search", display(tout); display_enodes_lbls(tout););
        TRACE("search_detail", m_asserted_formulas.display(tout););
        init_search();//初始化搜索
        flet<bool> l(m_searching, true);
        TRACE("after_init_search", display(tout););
        IF_VERBOSE(2, verbose_stream() << "(smt.searching)\n";);
        TRACE("search_lite", tout << "searching...\n";);
        lbool    status            = l_undef;
        unsigned curr_lvl          = m_scope_lvl;
        int restart_time=1;
        bool ls_flag=false;
        while (true) {
            SASSERT(!inconsistent());

            status = bounded_search();//受限搜索
            TRACE("search_bug", tout << "status: " << status << ", inconsistent: " << inconsistent() << "\n";);
            TRACE("assigned_literals_per_lvl", display_num_assigned_literals_per_lvl(tout);
                  tout << ", num_assigned: " << m_assigned_literals.size() << "\n";);
            if(!ls_flag&&m_timer.get_seconds()>10){
#ifdef IDL_DEBUG
                std::cout<<"begin local search  "<<m_timer.get_seconds()<<"\n";
#endif
                ls_flag=true;
                m_ls_solver->local_search();
                if(m_ls_solver->_best_found_hard_cost==0){std::cout<<"local search sat\n"<<m_timer.get_seconds()<<"\n";return l_true;}
#ifdef IDL_DEBUG
                std::cout<<"end local search  "<<m_timer.get_seconds()<<"\n";
#endif
            }
            // std::cout<<"restart_time "<<restart_time++<<"  time: "<<m_timer.get_seconds()<<"\n";
            if (!restart(status, curr_lvl)) {//如果受限搜索结束了就调用重启
                break;
            }            
        }

        TRACE("guessed_literals",
              expr_ref_vector guessed_lits(m);
              get_guessed_literals(guessed_lits);
              tout << guessed_lits << "\n";);
        end_search();
        return status;
    }
    //重启,在search中调用
    bool context::restart(lbool& status, unsigned curr_lvl) {
        SASSERT(status != l_true || !inconsistent());

        reset_model();

        if (m_last_search_failure != OK) {
            return false;
        }
        if (status == l_false) {
            return false;
        }
        if (status == l_true && !m_qmanager->has_quantifiers()) {
            return false;
        }
        if (status == l_true && m_qmanager->has_quantifiers()) {
            // possible outcomes   DONE l_true, DONE l_undef, CONTINUE 可能的结果，DONE true，undef，CONTINUE
            mk_proto_model();
            quantifier_manager::check_model_result cmr = quantifier_manager::UNKNOWN;
            if (m_proto_model.get()) {
                cmr = m_qmanager->check_model(m_proto_model.get(), m_model_generator->get_root2value());
            }
            switch (cmr) {
            case quantifier_manager::SAT:
                return false;
            case quantifier_manager::UNKNOWN:
                IF_VERBOSE(2, verbose_stream() << "(smt.giveup quantifiers)\n";);
                // giving up
                m_last_search_failure = QUANTIFIERS;
                status = l_undef;
                return false;
            default:
                break;
            }
        }
        inc_limits();
        if (status == l_true || !m_fparams.m_restart_adaptive || m_agility < m_fparams.m_restart_agility_threshold) {
            SASSERT(!inconsistent());
            log_stats();
            // execute the restart
            m_stats.m_num_restarts++;
            m_num_restarts++;
            if (m_scope_lvl > curr_lvl) {
                pop_scope(m_scope_lvl - curr_lvl);
                SASSERT(at_search_level());
            }
            for (theory* th : m_theory_set) {
                if (!inconsistent()) th->restart_eh();
            }
            TRACE("mbqi_bug_detail", tout << "before instantiating quantifiers...\n";);
            if (!inconsistent()) {
                m_qmanager->restart_eh();
            }
            if (inconsistent()) {
                VERIFY(!resolve_conflict());
                status = l_false;
                return false;
            }
            if (m_num_restarts >= m_fparams.m_restart_max) {
                status = l_undef;
                m_last_search_failure = NUM_CONFLICTS;
                return false;
            }
        }
        if (m_fparams.m_simplify_clauses)
            simplify_clauses();
        if (m_fparams.m_lemma_gc_strategy == LGC_AT_RESTART)
            del_inactive_lemmas();

        status = l_undef;
        return true;
    }
    //将counter加一，如果counter超过上限则重置,在bounded search中计数遇到冲突的次数
    void context::tick(unsigned & counter) const {
        counter++;
        if (counter > m_fparams.m_tick) {
            IF_VERBOSE(3, verbose_stream() << "(smt.working";
                       verbose_stream() << " :conflicts " << m_num_conflicts;
                       // verbose_stream() << " lemma avg. activity: " << get_lemma_avg_activity();
                       if (m_fparams.m_restart_adaptive)
                       verbose_stream() << " :agility " << m_agility;
                       verbose_stream() << ")" << std::endl; verbose_stream().flush(););
            TRACE("assigned_literals_per_lvl", display_num_assigned_literals_per_lvl(tout); tout << "\n";);
            counter = 0;
        }
    }
    //受限搜索，这是搜索部分的核心代码!!!
    lbool context::bounded_search() {
        unsigned counter = 0;

        TRACE("bounded_search", tout << "starting bounded search...\n";);

        while (true) {
            while (!propagate()) {//当还不需要用decide操作，目前出现了冲突，并且尚未超出资源
                TRACE_CODE({
                    static bool first_propagate = true;
                    if (first_propagate) {
                        first_propagate = false;
                        TRACE("after_first_propagate", display(tout););
                    }
                });
                //此处在做归结操作，学习子句，回溯
                tick(counter);//将counter加一，如果超过上限就重置counter，并且打印搜索信息

                if (!resolve_conflict())//归结冲突返回false说明当前的公式不可满足
                    return l_false;

                SASSERT(m_scope_lvl >= m_base_lvl);//要保证决策层>=base层

                if (!inconsistent()) {//如果目前还是一致的，并且满足如下情况，则返回搜索状态为unknown
                    if (resource_limits_exceeded())//资源超出
                        return l_undef;

                    if (get_cancel_flag())//被取消
                        return l_undef;

                    if (m_num_conflicts_since_restart > m_restart_threshold && m_scope_lvl - m_base_lvl > 2) {
                        TRACE("search_bug", tout << "bounded-search return undef, inconsistent: " << inconsistent() << "\n";);
                        return l_undef; // restart 如果在一次重启之后的冲突数大于阈值 并且 决策层大于base层+2
                    }

                    if (m_num_conflicts > m_fparams.m_max_conflicts) {
                        TRACE("search_bug", tout << "bounded-search return undef, inconsistent: " << inconsistent() << "\n";);
                        m_last_search_failure = NUM_CONFLICTS;
                        return l_undef;//如果总冲突数大于上限，返回undef
                    }
                }

                if (m_num_conflicts_since_lemma_gc > m_lemma_gc_threshold &&
                    (m_fparams.m_lemma_gc_strategy == LGC_FIXED || m_fparams.m_lemma_gc_strategy == LGC_GEOMETRIC)) {
                    del_inactive_lemmas();//删除一些活跃度低的lemma
                }

                m_dyn_ack_manager.propagate_eh();//动态acker归结
                CASSERT("dyn_ack", check_clauses(m_lemmas) && check_clauses(m_aux_clauses));
            }
            //跳出传播的原因有2个：需要decide； 资源耗尽，需要返回unknown
            if (resource_limits_exceeded() && !inconsistent()) {
                return l_undef;//如果资源耗尽并且还一致，则返回unknown
            }

            if (get_cancel_flag())
                return l_undef;//被取消了，返回unknown

            if (m_base_lvl == m_scope_lvl && m_fparams.m_simplify_clauses)
                simplify_clauses();//如果在最底层才能化简子句
            //进入decide
            if (!decide()) {//进行决策操作，如果没有case_split可以操作，则判断是否已经不可满足或者已经可满足或者要放弃
                if (inconsistent()) //如果没有可以case_split时是不一致的说明是不可满足的，因为已经是完整赋值了
                    return l_false;
                final_check_status fcs = final_check();//目前已经是完整赋值，需要进行最终检测
                TRACE("final_check_result", tout << "fcs: " << fcs << " last_search_failure: " << m_last_search_failure << "\n";);
                switch (fcs) {
                case FC_DONE:
                    log_stats();
                    return l_true;
                case FC_CONTINUE:
                    break;
                case FC_GIVEUP:
                    return l_undef;
                }
            }

            if (resource_limits_exceeded() && !inconsistent()) {//在decide完成之后还需要检测是否是在一致的情况下的资源耗尽，如果是的话需要返回unknown
                return l_undef;
            }
        }
    }
    //判断是否已经资源用尽
    bool context::resource_limits_exceeded() {
        if (m_searching) {
            // Some of the flags only make sense to check when searching.
            // For example, the timer is only started in init_search(). 某些flag只在搜索的时候有意义，例如timer(计时器)只在init_search时开始
            if (m_last_search_failure != OK)
                return true;

            if (get_cancel_flag()) {
                m_last_search_failure = CANCELED;
                return true;
            }

            if (m_progress_callback) {//如果使用进程回调
                m_progress_callback->fast_progress_sample();//调用进程回调函数判断是否资源超出
                if (m_fparams.m_progress_sampling_freq > 0 && m_timer.ms_timeout(m_next_progress_sample + 1)) {
                    m_progress_callback->slow_progress_sample();
                    m_next_progress_sample = (unsigned)(m_timer.get_seconds() * 1000) + m_fparams.m_progress_sampling_freq;
                }
            }
        }

        if (get_cancel_flag()) {//搜索被取消了
            m_last_search_failure = CANCELED;
            return true;
        }

        if (memory::above_high_watermark()) {//如果使用的内存量已经超过内存水位，则返回内存超出的失败
            m_last_search_failure = MEMOUT;
            return true;
        }

        return false;
    }
    //在完整赋值状态下进行最终检测，相当于检测理论是否可以满足,在bound_search没有可以赋值时调用，在
    final_check_status context::final_check() {
        TRACE("final_check", tout << "final_check inconsistent: " << inconsistent() << "\n"; display(tout); display_normalized_enodes(tout););
        CASSERT("relevancy", check_relevancy());
        
        if (m_fparams.m_model_on_final_check) {
            mk_proto_model();
            model_pp(std::cout, *m_proto_model);
            std::cout << "END_OF_MODEL\n";
            std::cout.flush();
        }

        m_stats.m_num_final_checks++;
        TRACE("final_check_stats", tout << "m_stats.m_num_final_checks = " << m_stats.m_num_final_checks << "\n";);

        final_check_status ok = m_qmanager->final_check_eh(false);
        if (ok != FC_DONE)
            return ok;

        m_incomplete_theories.reset();

        unsigned old_idx          = m_final_check_idx;
        unsigned num_th           = m_theory_set.size();//理论的个数
        unsigned range            = num_th + 1;
        final_check_status result = FC_DONE;
        failure  f                = OK;

        do {
            TRACE("final_check_step", tout << "processing: " << m_final_check_idx << ", result: " << result << "\n";);
            final_check_status ok;//ok是最终检测的状态
            if (m_final_check_idx < num_th) {//检测的是理论，此时check_idx指向的是理论
                theory * th = m_theory_set[m_final_check_idx];
                IF_VERBOSE(100, verbose_stream() << "(smt.final-check \"" << th->get_name() << "\")\n";);
                ok = th->final_check_eh();//理论的最终检测
                TRACE("final_check_step", tout << "final check '" << th->get_name() << " ok: " << ok << " inconsistent " << inconsistent() << "\n";);
                if (ok == FC_GIVEUP) {//如果理论检测的结果是放弃，则失败的是理论
                    f  = THEORY;
                    m_incomplete_theories.push_back(th);//将该理论加入不完整理论
                }
            }
            else {//检测的是量词
                ok = m_qmanager->final_check_eh(true);
                TRACE("final_check_step", tout << "quantifier  ok: " << ok << " " << "inconsistent " << inconsistent() << "\n";);
            }

            m_final_check_idx = (m_final_check_idx + 1) % range;//循环计数
            // IF_VERBOSE(1000, verbose_stream() << "final check status: " << ok << "\n";);

            switch (ok) {
            case FC_DONE://如果是done则什么都不做
                break;
            case FC_GIVEUP:
                result = FC_GIVEUP;//如果是giveup则记录在result中
                break;
            case FC_CONTINUE:
                return FC_CONTINUE;//如果是continue则直接返回
                break;
            }
        }
        while (m_final_check_idx != old_idx);//直到把所有理论都扫一遍

        TRACE("final_check_step", tout << "result: " << result << "\n";);

        if (can_propagate()) {//如果尚且可以传播，则返回最终检测状态是continue
            TRACE("final_check_step", tout << "can propagate: continue...\n";);
            return FC_CONTINUE;
        }

        SASSERT(result != FC_DONE || check_th_diseq_propagation());
        TRACE("final_check_step", tout << "RESULT final_check: " << result << "\n";);
        if (result == FC_GIVEUP && f != OK)//如果结果是giveup并且f不是OK，说明是在理论检测时得到的giveup，则要把失败的原因归为f，即理论
            m_last_search_failure = f;
        return result;
    }
    //检测proof，调用proof_checker.check，在resolve_conflict中验证失败的证明
    void context::check_proof(proof * pr) {
        if (m.proofs_enabled() && m_fparams.m_check_proof) {
            proof_checker pf(m);
            expr_ref_vector side_conditions(m);
            pf.check(pr, side_conditions);
        }
    }
    //遗忘当前层的变量的phase，在冲突归结中被调用，将本层赋值的所有文字的phase都设为不可available，即不可获取其值,在resolve_conflict中调用
    void context::forget_phase_of_vars_in_current_level() {
        unsigned head = m_scope_lvl == 0 ? 0 : m_scopes[m_scope_lvl - 1].m_assigned_literals_lim;
        unsigned sz   = m_assigned_literals.size();
        for (unsigned i = head; i < sz; i++) {
            literal l  = m_assigned_literals[i];
            bool_var v = l.var();
            TRACE("forget_phase", tout << "forgetting phase of l: " << l << "\n";);
            m_bdata[v].m_phase_available = false;//将上一层的已赋值文字到所有已赋值文字之间的所有文字，它们的phase_available设为false，即不可以获取其phase
        }
    }

//冲突归结，核心部分!!!
    bool context::resolve_conflict() {
        m_stats.m_num_conflicts++;
        m_num_conflicts ++;
        m_num_conflicts_since_restart ++;
        m_num_conflicts_since_lemma_gc ++;
        switch (m_conflict.get_kind()) {
        case b_justification::CLAUSE:
        case b_justification::BIN_CLAUSE:
            m_stats.m_num_sat_conflicts++;
            break;
        default:
            break;
        }
        if (m_fparams.m_phase_selection == PS_THEORY || 
            m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE || 
            m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE2)
            forget_phase_of_vars_in_current_level();//如果选择phase的策略是如上3种，则需要遗忘本层中的phase，即本层的phase不可available
        m_atom_propagation_queue.reset();
        m_eq_propagation_queue.reset();
        m_th_eq_propagation_queue.reset();
        m_th_diseq_propagation_queue.reset();
        if (m_conflict_resolution->resolve(m_conflict, m_not_l)) {
            unsigned new_lvl = m_conflict_resolution->get_new_scope_lvl();
            unsigned num_lits = m_conflict_resolution->get_lemma_num_literals();//num_lits是lemma中的文字数量
            literal * lits    = m_conflict_resolution->get_lemma_literals();//lits中存放的是lemma中的文字

            SASSERT(num_lits > 0);
            unsigned conflict_lvl = get_assign_level(lits[0]);
            SASSERT(conflict_lvl <= m_scope_lvl);

            // When num_lits == 1, then the default behavior is to go
            // to base-level. If the problem has quantifiers, it may be
            // too expensive to do that, since all instances will need to
            // be recreated. If that is the case, I store the assertions in
            // a special vector and keep reasserting whenever I backtrack.
            // Moreover, I backtrack only one level.
            //当lemma中文字数为1，则默认行为是回退到base层，如果问题中带有量词，则做该操作可能会很昂贵。
            //如果那样的话，我将断言存在一个特殊数组中，并且每当回退时都重新断言。
            //此外，只回退一层
            bool delay_forced_restart =
                m_fparams.m_delay_units &&
                internalized_quantifiers() &&
                num_lits == 1 &&
                conflict_lvl > m_search_lvl + 1 &&
                !m.proofs_enabled() &&
                m_units_to_reassert.size() < m_fparams.m_delay_units_threshold;

            if (delay_forced_restart) {
                new_lvl = conflict_lvl - 1;
            }

            // Some of the literals/enodes of the conflict clause will be destroyed during
            // backtracking, and will need to be recreated. However, I want to keep
            // the generation number for enodes that are going to be recreated. See
            // comment in cache_generation(unsigned).
            //冲突子句中的一些文字或enode会在回退的过程中被破坏，并且需要被重新创造
            //但是，又想要在它们将要被重新构造时，保持enode的生成号。
            //这些生成号会被存在m_cached_generation中
            if (m_conflict_resolution->get_lemma_intern_lvl() > new_lvl)
                cache_generation(num_lits, lits, new_lvl);

            SASSERT(new_lvl < m_scope_lvl);
            TRACE("resolve_conflict_bug",
                  tout << "m_scope_lvl: " << m_scope_lvl << ", new_lvl: " << new_lvl << ", lemma_intern_lvl: " << m_conflict_resolution->get_lemma_intern_lvl() << "\n";
                  tout << "num_lits: " << num_lits << "\n";
                  for (unsigned i = 0; i < num_lits; i++) {
                      literal l = lits[i];
                      tout << l << " ";
                      display_literal_smt2(tout, l);
                      tout << ", ilvl: " << get_intern_level(l.var()) << "\n"
                           << mk_pp(bool_var2expr(l.var()), m) << "\n";
                  });

            if (m.has_trace_stream() && !m_is_auxiliary) {
                m.trace_stream() << "[conflict] ";
                display_literals(m.trace_stream(), num_lits, lits);
                m.trace_stream() << "\n";
            }//一些打印信息

#ifdef Z3DEBUG
            expr_ref_vector expr_lits(m);
            bool_vector   expr_signs;
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = lits[i];
                if (get_assignment(l) != l_false) {
                    std::cout << l << " " << get_assignment(l) << "\n";
                }
                SASSERT(get_assignment(l) == l_false);
                expr_lits.push_back(bool_var2expr(l.var()));
                expr_signs.push_back(l.sign());
            }
#endif
            proof * pr = nullptr;
            if (m.proofs_enabled()) {//如果使用了proof，则需要获取lemma的证明
                pr = m_conflict_resolution->get_lemma_proof();
                // check_proof(pr);
                TRACE("context_proof", tout << mk_ll_pp(pr, m););
                TRACE("context_proof_hack",
                      static ast_mark visited;
                      ast_ll_pp(tout, m, pr, visited););
            }
            // I invoke pop_scope_core instead of pop_scope because I don't want
            // to reset cached generations... I need them to rebuild the literals
            // of the new conflict clause.
            //调用了pop_scope_core而不是pop_scope，因为我不想重置cached generations，在重建 新冲突子句 中的 文字 时需要cached_generations
            if (relevancy()) record_relevancy(num_lits, lits);//将相关性记录下来放在m_relevant_conflict_literals中，在冲突归结期间弹出的scope内，文字可能已被标记为相关。 这个可能会导致量词实例化错过 相关性引发器，并因此导致不一致性
            unsigned num_bool_vars = pop_scope_core(m_scope_lvl - new_lvl);//**回退到new_lvl层**
            SASSERT(m_scope_lvl == new_lvl);
            // the logical context may still be in conflict after
            // clauses are reinitialized in pop_scope.
            //子句在pop_scope被重新初始化之后，逻辑context可能还是冲突的
            if (m_conflict_resolution->get_lemma_intern_lvl() > m_scope_lvl) {//如果冲突归结的lemma层大于当前层
                expr * * atoms         = m_conflict_resolution->get_lemma_atoms();
                for (unsigned i = 0; i < num_lits; i++) {//遍历lemma中的文字
                    literal l   = lits[i];
                    if (l.var() >= static_cast<int>(num_bool_vars)) {
                        // This boolean variable was deleted during backtracking, it need to be recreated.
                        // Remark: atom may be a negative literal (not a). Z3 creates Boolean variables for not-gates that
                        // are nested in terms. Example: let f be a uninterpreted function from Bool -> Int.
                        // Then, given the term (f (not a)), Z3 will create a boolean variable for (not a) when internalizing (f (not a)).
                        //该布尔变量在回退过程中被删除了，因此它需要重新被构造
                        //注意：原子可能是一个负文字(not a)。Z3为嵌套在term中的非门创建布尔变量，例如：假设f是一个未解释函数bool->Int
                        //则给定term f((not a))，当中间化该term，Z3会为(not a)创造一个布尔变量
                        expr * atom     = atoms[i];
                        internalize(atom, true);
                        // If atom is actually a negative literal (not a), then get_bool_var will return return null_bool_var.如果atom是一个负文字，则get_bool_var会返回一个空布尔变量
                        // Thus, we must use get_literal instead. This was a bug/crash in Z3 <= 4.0 因此 需要使用get_literal
                        literal new_l = get_literal(atom);
                        if (l.sign())
                            new_l.neg();
                        // For reference, here is the buggy version
                        // BEGIN BUGGY VERSION
                        // bool_var v = get_bool_var(atom);
                        // CTRACE("resolve_conflict_crash", v == null_bool_var, tout << mk_ismt2_pp(atom, m) << "\n";);
                        // SASSERT(v != null_bool_var);
                        // literal new_l   = literal(v, l.sign());
                        // END BUGGY VERSION
                        lits[i]         = new_l;//更正lits中的文字
                    }
                }
            }
            if (relevancy()) restore_relevancy(num_lits, lits);//恢复相关性
            // Resetting the cache manually because I did not invoke pop_scope, but pop_scope_core 需要手动重置cache，因为没有使用pop_scope
            reset_cache_generation();
            TRACE("resolve_conflict_bug",
                  tout << "AFTER m_scope_lvl: " << m_scope_lvl << ", new_lvl: " << new_lvl << ", lemma_intern_lvl: " <<
                  m_conflict_resolution->get_lemma_intern_lvl() << "\n";
                  tout << "num_lits: " << num_lits << "\n";
                  for (unsigned i = 0; i < num_lits; i++) {
                      literal l = lits[i];
                      tout << l << " ";
                      display_literal(tout, l);
                      tout << ", ilvl: " << get_intern_level(l.var()) << "\n"
                           << mk_pp(bool_var2expr(l.var()), m) << "\n";
                  });
#ifdef Z3DEBUG
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = lits[i];
                if (expr_signs[i] != l.sign()) {
                    expr* real_atom;
                    VERIFY(m.is_not(expr_lits.get(i), real_atom));
                    // the sign must have flipped when internalizing
                    CTRACE("resolve_conflict_bug", real_atom != bool_var2expr(l.var()), tout << mk_pp(real_atom, m) << "\n" << mk_pp(bool_var2expr(l.var()), m) << "\n";);
                    SASSERT(real_atom == bool_var2expr(l.var()));
                }
                else {
                    SASSERT(expr_lits.get(i) == bool_var2expr(l.var()));
                }
            }
#endif
            justification * js = nullptr;
            if (m.proofs_enabled()) {
                js = alloc(justification_proof_wrapper, *this, pr, false);
            }
#if 0
            {
                static unsigned counter = 0;
                static uint64_t total = 0;
                static unsigned max = 0;
                counter++;
                total += num_lits;
                if (num_lits > max) {
                    max = num_lits;
                }
                if (counter % 1000 == 0) {
                    verbose_stream() << "[sat] avg. clause size: " << ((double) total/(double) counter) << ", max: " << max << std::endl;
                    for (unsigned i = 0; i < num_lits; i++) {
                        literal l = lits[i];
                        verbose_stream() << l.sign() << " " << mk_pp(bool_var2expr(l.var()), m) << "\n";
                    }
                }
            }
#endif
            mk_clause(num_lits, lits, js, CLS_LEARNED);
            if (delay_forced_restart) {
                SASSERT(num_lits == 1);
                expr * unit     = bool_var2expr(lits[0].var());
                bool unit_sign  = lits[0].sign();
                m_units_to_reassert.push_back(unit);//只有在冲突归结resolve_conflict中，lemma中文字数位1，会加入units_to_reassert
                m_units_to_reassert_sign.push_back(unit_sign);
                TRACE("reassert_units", tout << "asserting #" << unit->get_id() << " " << unit_sign << " @ " << m_scope_lvl << "\n";);
            }

            m_conflict_resolution->release_lemma_atoms();//释放lemma中的原子，即重置lemma
            TRACE("context_lemma", tout << "new lemma: ";
                  literal_vector v(num_lits, lits);
                  std::sort(v.begin(), v.end());
                  for (unsigned i = 0; i < num_lits; i++) {
                      display_literal(tout, v[i]);
                      tout << "\n";
                      v[i].display(tout, m, m_bool_var2expr.c_ptr());
                      tout << "\n\n";
                  }
                  tout << "\n";);
            decay_bvar_activity();
            update_phase_cache_counter();
            return true;
        }
        else if (m_fparams.m_clause_proof && !m.proofs_enabled()) {
            m_unsat_proof = m_clause_proof.get_proof(inconsistent());//否则归结之后显示当前公式是不可满足的，并且不使用proof
        }
        else if (m.proofs_enabled()) {//如果需要记录下不可满足的证明，则将lemma作为不可满足的原因记录在unsat_proof中
            m_unsat_proof = m_conflict_resolution->get_lemma_proof();
            check_proof(m_unsat_proof);
        }
        return false;//归结之后说明原公式不可满足，即冲突归结失败
    }

    /*
      \brief we record and restore relevancy information for literals in conflict clauses.
      A literal may have been marked relevant within the scope that gets popped during
      conflict resolution. In this case, the literal is no longer marked as relevant after
      the pop. This can cause quantifier instantiation to miss relevant triggers and thereby
      cause incompleteness.
      我们记录并恢复 冲突子句中文字 的相关信息
      在冲突归结期间弹出的scope内，文字可能已被标记为相关。
      这个可能会导致量词实例化错过 相关性引发器，并因此导致不一致性，在resolve_conflict中使用
     */
    void context::record_relevancy(unsigned n, literal const* lits) {
        m_relevant_conflict_literals.reset();
        for (unsigned i = 0; i < n; ++i) {
            m_relevant_conflict_literals.push_back(is_relevant(lits[i]));
        }
    }
    //恢复相关性，逐个遍历0～n号lits中的文字，如果m_relevant_confliict_literal中被标记了，但是lits中的第i号没有标记，则为lits的相应的位置标记
    void context::restore_relevancy(unsigned n, literal const* lits) {
        for (unsigned i = 0; i < n; ++i) {
            if (m_relevant_conflict_literals[i] && !is_relevant(lits[i])) {
                mark_as_relevant(lits[i]);
            }
        }
    }
    //获取relevant文字的标签，记录在result中
    void context::get_relevant_labels(expr* cnstr, buffer<symbol> & result) {
        if (m_fparams.m_check_at_labels) {
            check_at_labels checker(m);
            if (cnstr && !checker.check(cnstr)) {
                warning_msg("Boogie generated formula that can require multiple '@' labels in a counter-example");
            }
            else {
                unsigned nf = m_asserted_formulas.get_num_formulas();
                for (unsigned i = 0; i < nf; ++i) {
                    expr* fml = m_asserted_formulas.get_formula(i);
                    if (!checker.check(fml)) {
                        warning_msg("Boogie generated formula that can require multiple '@' labels in a counter-example");
                        break;
                    }
                }
            }
        }

        SASSERT(!inconsistent());
        for (expr * curr : m_b_internalized_stack) { 
            if (is_relevant(curr) && get_assignment(curr) == l_true) {
                // if curr is a label literal, then its tags will be copied to result.
                m.is_label_lit(curr, result);
            }
        }
    }

    /**
       \brief Collect relevant literals that may be used to block the current assignment.
       If at_lbls is true, then only labels that contains '@' are considered. (This is a hack for Boogie).
       This hack is also available in the Simplify theorem prover.
       收集可能被用来block当前赋值的relevant文字
       如果at_lbls是true，则只有包含@的标签会被考虑，这个技巧也可以在 化简定理证明器 中找到。
    */
    void context::get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result) {
        SASSERT(!inconsistent());
        buffer<symbol> lbls;
        for (expr * curr : m_b_internalized_stack) {
            if (is_relevant(curr) && get_assignment(curr) == l_true) {
                lbls.reset();
                if (m.is_label_lit(curr, lbls)) {
                    bool include = false;
                    if (at_lbls) {
                        // include if there is a label with the '@' sign. 如果存在一个标记带有@符号，则会被包含
                        for (symbol const& s : lbls) {
                            if (s.contains('@')) {
                                include = true;
                                break;
                            }
                        }
                    }
                    else {
                        include = true;
                    }
                    if (include)
                        result.push_back(curr);
                }
            }
        }
    }

    /**
       \brief Store in result the (relevant) literal assigned by the
       logical context.
       遍历b_internalized_stack(被中间化的布尔表达式栈)中的表达式，将逻辑context赋值的（相关）文字存储在结果result中。（注意此处只记录了relevant文字）无调用
    */
    void context::get_relevant_literals(expr_ref_vector & result) {
        SASSERT(!inconsistent());
        unsigned sz = m_b_internalized_stack.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = m_b_internalized_stack.get(i);
            if (is_relevant(curr)) {
                switch (get_assignment(curr)) {
                case l_true:
                    result.push_back(curr);
                    break;
                case l_false:
                    result.push_back(m.mk_not(curr));
                    break;
                default:
                    break;
                }
            }
        }
    }

    /**
       \brief Store the current set of guessed literals (i.e., case splits).
       存储猜测文字的当前集合在reuslt中（即case split文字，也就是guessed的文字），在search中被调用
    */
    void context::get_guessed_literals(expr_ref_vector & result) {
        // The literals between [m_base_lvl, m_search_lvl) are not guesses but assumptions.在[m_base_lvl,m_search_lvl)之间层的文字不是guess 而是 假设
        SASSERT(m_base_lvl <= m_scopes.size());
        if (m_search_lvl == m_scopes.size()) {
            // do nothing... there are guesses...
        }
        for (unsigned i = m_search_lvl; i < m_scope_lvl; i++) {
            // This method assumes the first literal assigned in a non base scope level is a guess. 该方法的前提假设是在一个非base层被赋值的第一个文字是一个guess
            scope & s          = m_scopes[i];
            unsigned guess_idx = s.m_assigned_literals_lim;
            literal guess      = m_assigned_literals[guess_idx];
            SASSERT(get_justification(guess.var()).get_kind() == b_justification::AXIOM);
            expr_ref lit(m);
            literal2expr(guess, lit);
            result.push_back(std::move(lit));//将guess的文字存在result中
        }
    }

    /**
       \brief Undo object for bool var m_true_first field update.
       撤销bool变量m_true_first字段更新的对象
    */
    class set_true_first_trail : public trail<context> {
        bool_var m_var;
    public:
        set_true_first_trail(bool_var v):m_var(v) {}
        void undo(context & ctx) override {
            ctx.m_bdata[m_var].reset_true_first_flag();
        }
    };
    //设置变量v的m_true_first为真，将set_true_first_trail推进trail中，在assume_eq中调用
    void context::set_true_first_flag(bool_var v) {
        push_trail(set_true_first_trail(v));
        bool_var_data & d = m_bdata[v];
        d.set_true_first_flag();
    }
    //假设等式lhs和rhs是相等的,无调用
    bool context::assume_eq(enode * lhs, enode * rhs) {
        if (lhs->get_root() == rhs->get_root())
            return false; // it is not necessary to assume the eq. 如果lhs和rhs的根相同，则不必要假定等式
        expr * _lhs = lhs->get_owner();
        expr * _rhs = rhs->get_owner();
        expr * eq = mk_eq_atom(_lhs, _rhs);
        TRACE("assume_eq", tout << "creating interface eq:\n" << mk_pp(eq, m) << "\n";);
        if (m.is_false(eq)) {
            return false;
        }
        bool r = false;
        if (!b_internalized(eq)) {
            // I do not invoke internalize(eq, true), because I want to
            // mark the try_true_first flag before invoking theory::internalize_eq_eh.
            // Reason: Theories like arithmetic should be able to know if the try_true_first flag is
            // marked or not. They use this information to also mark auxiliary atoms such as:
            //  (<= (- x y) 0)
            //  (>= (- y x) 0)
            // for the new equality atom (= x y).
            //不会调用internalize，因为想要在调用理论的internalize_eq_eh之前 就先标记try_true_first
            //原因是：像算术之类的理论应该知道try_true_first是否已经被标记为真了。它们会使用这一信息来 为新的 等价原子标记 如下辅助原子
            if (m.is_eq(eq)) {
                internalize_formula_core(to_app(eq), true);
                bool_var v        = get_bool_var(eq);
                bool_var_data & d = get_bdata(v);
                d.set_eq_flag();
                set_true_first_flag(v);
                sort * s    = m.get_sort(to_app(eq)->get_arg(0));
                theory * th = m_theories.get_plugin(s->get_family_id());
                if (th)
                    th->internalize_eq_eh(to_app(eq), v);
            }
            else {
                internalize(eq, true);
            }
            r = true;
            m_stats.m_num_interface_eqs++;
            TRACE("assume_eq", tout << "new internalization.\n";);
        }
        bool_var v        = get_bool_var(eq);
        bool_var_data & d = m_bdata[v];
        if (!d.try_true_first()) {
            set_true_first_flag(v);
            r = true;
            TRACE("assume_eq", tout << "marked as ieq.\n";);
        }
        if (get_assignment(v) == l_undef) {
            TRACE("assume_eq", tout << "variable is unassigned.\n";);
            r = true;
        }
        if (relevancy() && !is_relevant(eq)) {
            TRACE("assume_eq", tout << "marking eq as relevant.\n";);
            mark_as_relevant(eq);
            r = true;
        }
        TRACE("assume_eq", tout << "variable value: " << get_assignment(v) << "\n";);
        TRACE("assume_eq", tout << "assume_eq result: " << r << "\n";);
        return r;
    }
    //判断一个enode n是否是被共享的，如果n的等价类包含一个父应用，则该变量是被共享的,未调用
    bool context::is_shared(enode * n) const {
        n = n->get_root();
        unsigned num_th_vars = n->get_num_th_vars();
        if (m.is_ite(n->get_owner())) {
            return true;
        }
        switch (num_th_vars) {
        case 0: {
            return false;
        }
        case 1: {
            if (m_qmanager->is_shared(n)) {
                return true;
            }

            // the variable is shared if the equivalence class of n
            // contains a parent application.
            // 如果n的等价类包含一个父应用，则该变量是被共享的

            theory_var_list * l = n->get_th_var_list();
            theory_id th_id     = l->get_id();

            for (enode * parent : enode::parents(n)) {
                app* p = parent->get_owner();
                family_id fid = p->get_family_id();
                if (fid != th_id && fid != m.get_basic_family_id()) {
                    TRACE("is_shared", tout << enode_pp(n, *this) 
                          << "\nis shared because of:\n" 
                          << enode_pp(parent, *this) << "\n";);
                    return true;
                }
            }

            // Some theories implement families of theories. Examples:
            // Arrays and Tuples.  For example, array theory is a
            // parametric theory, that is, it implements several theories:
            // (array int int), (array int (array int int)), ...
            //一些理论实现了理论类，例如：Array和Tuples，例如，数组理论是一个带参数的理论，即它实现了一些理论（数组 整数 整数）。。。
            // Example:
            //
            // a : (array int int)
            // b : (array int int)
            // x : int
            // y : int
            // v : int
            // w : int
            // A : (array (array int int) int)
            //
            // assert (= b (store a x v))
            // assert (= b (store a y w))
            // assert (not (= x y))
            // assert (not (select A a))
            // assert (not (select A b))
            // check
            //
            // In the example above, 'a' and 'b' are shared variables between
            // the theories of (array int int) and (array (array int int) int).
            // Remark: The inconsistency is not going to be detected if they are
            // not marked as shared.在例子中，'a'和‘b'是两个理论的共享变量，如果他们不被标记为共享的话，不一致是不会被检测到的
            return get_theory(th_id)->is_shared(l->get_var());
        }
        default:
            return true;
        }
    }
    //获得enode n在相应的理论中的value，调用相关理论的get_value方法
    bool context::get_value(enode * n, expr_ref & value) {
        sort * s      = m.get_sort(n->get_owner());
        family_id fid = s->get_family_id();
        theory * th   = get_theory(fid);
        if (th == nullptr)
            return false;
        return th->get_value(n, value);
    }
    //更新model，首先final_check一下，如果理论检测成功，则重置模型
    bool context::update_model(bool refinalize) {
        final_check_status fcs = FC_DONE;
        if (refinalize) {
            if (has_case_splits())
                return false;
            fcs = final_check();
            TRACE("opt", tout << (refinalize?"refinalize":"no-op") << " " << fcs << "\n";);
        }
        if (fcs == FC_DONE) {
            reset_model();
        }
        return false;
    }
    //为m_model用m_model_generator构造一个新的值，在get_model，restart,final_check中调用
    void context::mk_proto_model() {
        if (m_model || m_proto_model || has_case_splits()) return;//如果model已经存在就直接返回
        TRACE("get_model",
              display(tout);
              display_normalized_enodes(tout);
              display_enodes_lbls(tout);
              m_fingerprints.display(tout);
              );
        failure fl = get_last_search_failure();
        if (fl == MEMOUT || fl == CANCELED || fl == NUM_CONFLICTS || fl == RESOURCE_LIMIT) {//如果失败信息存在这些情况就先打印之前的失败信息
            TRACE("get_model", tout << "last search failure: " << fl << "\n";);   
        }     
        else if (m_fparams.m_model || m_fparams.m_model_on_final_check || 
                 (m_qmanager->has_quantifiers() && m_qmanager->model_based())) {//如果不存在上述错误信息，并且满足如下情况，就产生一个m_proto_model
            m_model_generator->reset();
            m_proto_model = m_model_generator->mk_model();
            m_qmanager->adjust_model(m_proto_model.get());
            TRACE("mbqi_bug", tout << "before complete_partial_funcs:\n"; model_pp(tout, *m_proto_model););
            m_proto_model->complete_partial_funcs(false);
            TRACE("mbqi_bug", tout << "before cleanup:\n"; model_pp(tout, *m_proto_model););
            m_proto_model->cleanup();
            TRACE("mbqi_bug", tout << "after cleanup:\n"; model_pp(tout, *m_proto_model););
            IF_VERBOSE(11, model_pp(verbose_stream(), *m_proto_model););
        }
    }
    //获取unsat的proof
    proof * context::get_proof() {        
        if (!m_unsat_proof) {
            m_unsat_proof = m_clause_proof.get_proof(inconsistent());//如果没有unsat_proof，就调用子句中获取不一致proof函数
        }
        TRACE("context", tout << m_unsat_proof << "\n";);
        return m_unsat_proof;
    }
    //逐个考虑所有internalized的数量，如果i是relevant并且i没有被定义，那么就是有case_splits
    bool context::has_case_splits() {
        for (unsigned i = get_num_b_internalized(); i-- > 0; ) {
            if (is_relevant(i) && get_assignment(i) == l_undef)
                return true;
        }
        return false;
    }
    //获取model到model ref中，在check_final中被使用
    void context::get_model(model_ref & mdl) {
        if (inconsistent()) 
            mdl = nullptr;
        else if (m_model.get()) 
            mdl = m_model.get();//如果m_model.get可以返回值则将其设为mdl
        else if (!m.inc())
            mdl = nullptr;
        else {
            mk_proto_model();
            if (!m_model && m_proto_model) {
                m_model = m_proto_model->mk_model();
                try {
                    add_rec_funs_to_model();
                }
                catch (...) {
                    // no op
                }                
            }
            mdl = m_model.get();
        }
    }
    //遍历所有的变量，将每个变量的赋值层数放在depth数组中，如果变量为null_bool_var，则为其设置为MAX,无调用
    void context::get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) {
        unsigned sz = vars.size(); 
        depth.resize(sz);
        for (unsigned i = 0; i < sz; ++i) {
            expr* v = vars[i];
            bool_var bv = m_expr2bool_var.get(v->get_id(), null_bool_var);
            depth[i] = bv == null_bool_var ? UINT_MAX : get_assign_level(bv);            
        }
    }
    //获取当前部分赋值的迹，无调用
    expr_ref_vector context::get_trail() {        
        expr_ref_vector result(get_manager());
        get_assignments(result);
        return result;
    }
    //获取最后一次失败原因，在mk_proto_model中被调用
    failure context::get_last_search_failure() const {
        return m_last_search_failure;
    }
    //向model中加入rec_funs,在get_model中被调用
    void context::add_rec_funs_to_model() {
        if (!m_model) return;
        recfun::util u(m);
        func_decl_ref_vector recfuns = u.get_rec_funs();
        for (func_decl* f : recfuns) {
            auto& def = u.get_def(f);
            expr* rhs = def.get_rhs();
            if (!rhs) continue;
            if (f->get_arity() == 0) {
                m_model->register_decl(f, rhs);
                continue;
            }			

            func_interp* fi = alloc(func_interp, m, f->get_arity());
            // reverse argument order so that variable 0 starts at the beginning.反转参数顺序，使变量0从开头开始 
            expr_ref_vector subst(m);
            for (unsigned i = 0; i < f->get_arity(); ++i) {
                subst.push_back(m.mk_var(i, f->get_domain(i)));
            }
            var_subst sub(m, true);
            expr_ref bodyr = sub(rhs, subst.size(), subst.c_ptr());

            fi->set_else(bodyr);
            m_model->register_decl(f, fi);
        }
        TRACE("model", tout << *m_model << "\n";);
    }

};


#ifdef Z3DEBUG
void pp(smt::context & c) {
    c.display(std::cout);
}
#endif
