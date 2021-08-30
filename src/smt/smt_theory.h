/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_theory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#pragma once

#include "ast/ast_pp.h"
#include "smt/smt_enode.h"
#include "smt/smt_quantifier.h"
#include "util/obj_hashtable.h"
#include "util/statistics.h"
#include<typeinfo>

namespace smt {
    class model_generator;
    class model_value_proc;

    class theory {
    protected:
        theory_id       m_id;
        context &       ctx;
        ast_manager &   m;
        enode_vector    m_var2enode;
        unsigned_vector m_var2enode_lim;
        unsigned        m_lazy_scopes;
        bool            m_lazy;

        friend class context;
        friend class arith_value;
    protected:

        /* ---------------------------------------------------
        
        In the logical context, expressions are 'internalized'. That
        is, the logical context creates auxiliary data-structures
        (e.g., enodes) and attach them to the expressions. The logical
        context does not know the internals of each theory. So, during
        the internalization process, it notifies the theory (plugin)
        whenever it finds an application with a theory function
        symbol.

        A theory variable created at scope level n must be deleted
        when scope level n is backtracked.

        The logical context uses the method is_attached_to_var
        to decide whether an enode is already associated with a theory 
        variable or not.
        在逻辑context中，表达式被中间化了。
        也就是说，逻辑context构造了辅助数据结构(enode) 并将其与表达式相关联。
        逻辑context并不知道每个理论的内部构件
        所以，在内化过程中，每当它找到了一个 带有理论函数符号 的app，它会提醒理论插件

        一个在n层被创造的理论变量，必须在当n层被回溯的时候被删除

        逻辑context使用了is_attched_to_var来确定一个enode是否已经关联了一个理论变量

        ------------------------------------------------------ */

        virtual theory_var mk_var(enode * n) {
            SASSERT(!is_attached_to_var(n));
            theory_var v = m_var2enode.size();
            m_var2enode.push_back(n);
            return v;
        }

        theory_var get_th_var(expr* e) const;

        theory_var get_th_var(enode* n) const {
            return n->get_th_var(get_id());
        }

        bool lazy_push();
        bool lazy_pop(unsigned& num_scopes);
        void force_push();
        
    public:
        /**
           \brief Return true if the given enode is attached to a
           variable of the theory.
           
           \remark The result is not equivalent to
           n->get_th_var(get_id()) != null_theory_var
           
           A theory variable v may be in the list of variables of n,
           but it may be inherited from another enode n' during an
           equivalence class merge. That is, get_enode(v) != n.
           如果指定的enode与理论的一个变量 相关联 则返回true
           该结果不等同于n->get_th_var(get_id()) != null_theory_var
           一个理论变量v可能在n的变量列表中，但是它可能是在一次等价类合并操作，从另外一个enode n'继承的，即get_enode(v)!=n
        */
        bool is_attached_to_var(enode const * n) const {
            theory_var v = n->get_th_var(get_id());
            return v != null_theory_var && get_enode(v) == n;
        }
    //用于追踪，打印信息
        struct scoped_trace_stream {
            ast_manager& m;
            
            scoped_trace_stream(ast_manager& m, std::function<void (void)>& fn): m(m) {
                if (m.has_trace_stream()) {
                    fn();
                }
            }

            scoped_trace_stream(theory& th, std::function<expr* (void)>& fn): m(th.get_manager()) {
                if (m.has_trace_stream()) {
                    expr_ref body(fn(), m);
                    th.log_axiom_instantiation(body);
                }
            }

            scoped_trace_stream(theory& th, std::function<literal_vector(void)>& fn): m(th.get_manager()) {
                if (m.has_trace_stream()) {
                    th.log_axiom_instantiation(fn());
                }
            }

            scoped_trace_stream(theory& th, literal_vector const& lits): m(th.get_manager()) {
                if (m.has_trace_stream()) {
                    th.log_axiom_instantiation(lits);
                }
            }

            scoped_trace_stream(theory& th, literal lit): m(th.get_manager()) {
                if (m.has_trace_stream()) {
                    literal_vector lits;
                    lits.push_back(lit);
                    th.log_axiom_instantiation(lits);
                }
            }

            scoped_trace_stream(theory& th, literal lit1, literal lit2): m(th.get_manager()) {
                if (m.has_trace_stream()) {
                    literal_vector lits;
                    lits.push_back(lit1);
                    lits.push_back(lit2);
                    th.log_axiom_instantiation(lits);
                }
            }

            scoped_trace_stream(theory& th, std::function<literal(void)>& fn): m(th.get_manager()) {
                if (m.has_trace_stream()) {
                    literal_vector ls;
                    ls.push_back(fn());
                    th.log_axiom_instantiation(ls);
                }
            }
            
            ~scoped_trace_stream() {
                if (m.has_trace_stream()) {
                    m.trace_stream() << "[end-of-instance]\n";
                }
            }
        };

        struct if_trace_stream {
            ast_manager& m;
            
            if_trace_stream(ast_manager& m, std::function<void (void)>& fn): m(m) {
                if (m.has_trace_stream()) {
                    fn();
                }
            }
        };        

    protected:
        /**
           \brief Return true if the theory uses default internalization:
           "the internalization of an application internalizes all arguments".
           Theories like arithmetic do not use default internalization.
           For example, in the application (+ a (+ b c)), no enode is created
           for (+ b c).
           如果理论使用了默认 中间化 则返回true：
           一个app的内化过程会内化所有参数。
           像算术之类的理论不会使用默认内化过程。
           例如在app (+ a (+ b c))中，不会为(+ b c)创造enode
        */
        virtual bool default_internalizer() const {
            return true;
        }

        /**
           \brief This method is invoked by the logical context when
           atom is being internalized. The theory may return false if it 
           does not want to implement the given predicate symbol.

           After the execution of this method the given atom must be
           associated with a new boolean variable.
           当原子atom正在被内化时，该方法被逻辑context调用。
           如果理论不愿意实现给定的谓词符号，则理论可能返回false
           在执行该方法之后，给定原子必须关联到一个新的布尔变量
        */
        virtual bool internalize_atom(app * atom, bool gate_ctx) = 0;

        /**
           \brief This method is invoked by the logical context
           after the given equality atom is internalized.
           在给定等式原子被中间化后，该方法被逻辑context调用
        */
        virtual void internalize_eq_eh(app * atom, bool_var v) {
        }
                                    
        /**
           \brief This method is invoked by the logical context when
           the term is being internalized. The theory may return false
           if it does not want to implement the given function symbol.
           
           After the execution of this method the given term must be 
           associated with a new enode.
           当term正在被中间化，该方法被逻辑context调。
           如果理论不想实现给定的函数符号，则理论可能返回false
           在执行该方法之后，给定的term必须被关联到一个新的enode
        */
        virtual bool internalize_term(app * term) = 0;

        /**
           \brief Apply (interpreted) sort constraints on the given enode.
           在给定enode上应用（解释的）类型约束
        */
        virtual void apply_sort_cnstr(enode * n, sort * s) {
        }

        /**
           \brief This method is invoked when a truth value is 
           assigned to the given boolean variable.
           当给定bool变量被赋值时，该方法被调用，core提醒理论一个atom被赋值了!!
        */
        virtual void assign_eh(bool_var v, bool is_true) {
        }

        /**
           \brief use the theory to determine phase of the variable.
           用理论来确定给定布尔变量的phase
         */
        virtual lbool get_phase(bool_var v) {
            return l_undef;
        }

        /**
           \brief Equality propagation (v1 = v2): Core -> Theory
           将等式（v1=v2）从core传播给理论
        */
        virtual void new_eq_eh(theory_var v1, theory_var v2) = 0;

        /**
           \brief Return true if the theory does something with the
           disequalities implied by the core.
           如果理论对由core推出的不等式做了一些事，则返回true
        */
        virtual bool use_diseqs() const { 
            return true; 
        }

        /**
           \brief Disequality propagation (v1 /= v2): Core -> Theory
           不等式传播，core提醒theory一个不等式(v1!=v2)被传播了
        */
        virtual void new_diseq_eh(theory_var v1, theory_var v2) = 0;

        /**
           \brief This method is invoked when the theory application n
           is marked as relevant.
           当理论app n被标记为相关，该方法被调用
         */
        virtual void relevant_eh(app * n) {
        }
        
        /**
           \brief This method is invoked when a new backtracking point
           is created.
           当一个新的回溯点被创造时，该方法被调用!!，core提醒theory做了一个决策
        */
        virtual void push_scope_eh();

        /**
           \brief This method is invoked during backtracking.
           该方法在当回溯时该方法被调用!!core提醒theory一个决策需要被删除
        */
        virtual void pop_scope_eh(unsigned num_scopes);

        /**
           \brief This method is invoked when the logical context is being
           restarted.
           当逻辑context正在被重启时，调用该方法,即core提醒theory搜索过程正在重启
        */
        virtual void restart_eh() {
        }

        /**
           \brief This method is called by smt_context before the search starts
           to get any extra assumptions the theory wants to use.
           (See theory_str for an example)
           在搜索开始之前，smt_context会调用该方法来获得 理论 想要使用的附加假设
        */
        virtual void add_theory_assumptions(expr_ref_vector & assumptions) {
        }

        /**
           \brief This method is called from the smt_context when an unsat core is generated.
           The theory may change the answer to UNKNOWN by returning l_undef from this method.
           当一个unsat 核被生成时，smt_context会调用该方法
           理论可能通过该方法返回l_undef来将答案修改为unknown
        */
        virtual lbool validate_unsat_core(expr_ref_vector & unsat_core) {
            return l_false;
        }

        /**
           \brief This method is called from the smt_context when an unsat core is generated.
           The theory may tell the solver to perform iterative deepening by invalidating
           this unsat core and increasing some resource constraints.
           该方法是当一个unsat core被生成了，则从smt_context中调用。理论会告诉解算器执行迭代深化，通过使这个未满足的核心无效并增加一些资源约束
        */
        virtual bool should_research(expr_ref_vector & unsat_core) {
            return false;
        }

        /**
           \brief This method is invoked before the search starts.
           该方法会在搜索开始之前被调用
        */
        virtual void init_search_eh() {
        }

        /**
           \brief This method is invoked when the logical context assigned
           a truth value to all boolean variables and no inconsistency was 
           detected.
           当逻辑context对所有bool 变量都赋值了，并且没有发现不一致时，该方法被调用
        */
        virtual final_check_status final_check_eh() {
            return FC_DONE;
        }

        /**
           \brief Parametric theories (e.g. Arrays) should implement this method.
           See example in context::is_shared
           参数化理论应该实现该方法（如数组）
        */
        virtual bool is_shared(theory_var v) const {
            return false;
        }
    
        /**
           \brief Return true if the theory has something to propagate
            如果该理论有可以传播的东西，就返回true
        */
        virtual bool can_propagate() {
            return false;
        }
        
        /**
           \brief This method is invoked to give a theory a chance to perform
           theory propagation.
           该方法被调用来让理论求解器执行理论传播
        */
        virtual void propagate() {
        }
        
        /**
           \brief This method allows a theory to contribute to
           disequality propagation.
           该方法允许理论来为不等式传播贡献
        */
        virtual justification * why_is_diseq(theory_var v1, theory_var v2) {
            return nullptr;
        }

        /**
           \brief Just releases memory.
           释放内存
        */
        virtual void flush_eh() {
        }

        /**
           \brief This method is invoked when the logical context is being reset.
           当逻辑context正在被重置时，该方法被调用
        */
        virtual void reset_eh();

        // ----------------------------------------------------
        //
        // Model validation 模型验证
        //
        // ----------------------------------------------------

        virtual void validate_model(model& mdl) {}

        // ----------------------------------------------------
        //
        // Conflict resolution event handler 冲突归结事件处理
        //
        // ----------------------------------------------------
    public:
        /**
           \brief This method is invoked when a theory atom is used
           during conflict resolution. This allows the theory to bump
           the activity of the enodes contained in the given atom.
           当一个理论原子在冲突归结中被使用了，该方法被调用
           这使得该理论能够提高给定原子中所含enode的活性
        */
        virtual void conflict_resolution_eh(app * atom, bool_var v) {
        }


    public:
        theory(context& ctx, family_id fid);
        virtual ~theory();
        
        virtual void setup() {}

        virtual void init() {}

        theory_id get_id() const {
            return m_id;
        }

        family_id get_family_id() const {
            return m_id;
        }

        context & get_context() const {
            return ctx;
        }
        
        ast_manager & get_manager() const {
            return m;
        }

        smt_params const& get_fparams() const;

        enode * get_enode(theory_var v) const {
            SASSERT(v < static_cast<int>(m_var2enode.size()));
            return m_var2enode[v];
        }

        app * get_expr(theory_var v) const {
            return get_enode(v)->get_owner();
        }

        /**
           \brief Return the equivalence class representative 
           of the given theory variable.
           返回理论变量v所在的等价类的代表
        */
        theory_var get_representative(theory_var v) const {
            SASSERT(v != null_theory_var);
            theory_var r = get_enode(v)->get_root()->get_th_var(get_id());
            SASSERT(r != null_theory_var);
            return r;
        }

        /** 
            \brief Return true if the theory variable is the representative
            of its equivalence class.
            如果该理论变量是它所在等价类的代表，则返回true
        */
        bool is_representative(theory_var v) const {
            return get_representative(v) == v;
        }

        virtual bool is_safe_to_copy(bool_var v) const { return true; }
        
        unsigned get_num_vars() const {
            return m_var2enode.size();
        }

        unsigned get_old_num_vars(unsigned num_scopes) const {
            return m_var2enode_lim[m_var2enode_lim.size() - num_scopes];
        }
        
        virtual void display(std::ostream & out) const = 0;

        virtual void display_var2enode(std::ostream & out) const;
        
        virtual void collect_statistics(::statistics & st) const {
        }
        
        std::ostream& display_app(std::ostream & out, app * n) const;
        
        std::ostream& display_flat_app(std::ostream & out, app * n) const;
        
        std::ostream& display_var_def(std::ostream & out, theory_var v) const { return display_app(out, get_enode(v)->get_owner()); }
        
        std::ostream& display_var_flat_def(std::ostream & out, theory_var v) const { return display_flat_app(out, get_enode(v)->get_owner());  }

    protected:
        void log_axiom_instantiation(app * r, unsigned axiom_id = UINT_MAX, unsigned num_bindings = 0, 
                                     app * const * bindings = nullptr, unsigned pattern_id = UINT_MAX, 
                                     const vector<std::tuple<enode *, enode *>> & used_enodes = vector<std::tuple<enode *, enode*>>());

        void log_axiom_instantiation(expr * r, unsigned axiom_id = UINT_MAX, unsigned num_bindings = 0, 
                                     app * const * bindings = nullptr, unsigned pattern_id = UINT_MAX, 
                                     const vector<std::tuple<enode *, enode *>> & used_enodes = vector<std::tuple<enode *, enode*>>()) { 
            log_axiom_instantiation(to_app(r), axiom_id, num_bindings, bindings, pattern_id, used_enodes); 
        }

        void log_axiom_instantiation(literal_vector const& ls);

        void log_axiom_instantiation(app * r, unsigned num_blamed_enodes, enode ** blamed_enodes) {
            vector<std::tuple<enode *, enode *>> used_enodes;
            for (unsigned i = 0; i < num_blamed_enodes; ++i) {
                used_enodes.push_back(std::make_tuple(nullptr, blamed_enodes[i]));
            }
            log_axiom_instantiation(r, UINT_MAX, 0, nullptr, UINT_MAX, used_enodes);
        }

        void log_axiom_unit(app* r) {
            log_axiom_instantiation(r);
            m.trace_stream() << "[end-of-instance]\n";
        }

    public:
        /**
           \brief Assume eqs between variable that are equal with respect to the given table.
           Table is a hashtable indexed by the variable value.
           
           table.contains(v) should be true if there is v' in table such that assignment of
           v is equal to v'.

           This method assumes that class VarValueTable contains the methods:

           - void reset()
           - theory_var insert_if_not_there(theory_var v)
           假设 与给定表相等的变量 之间的等式
           表格是一个由变量值编码的哈希表

           如果存在一个表中的变量v'的赋值与v相等，则table.contains(v)要返回true
           该方法假设VarValueTable包含如下方法：
        */
        template<typename VarValueTable>
        bool assume_eqs(VarValueTable & table) {
            TRACE("assume_eqs", tout << "starting...\n";);
            table.reset();
            bool result   = false;
            int num       = get_num_vars();
            for (theory_var v = 0; v < num; v++) {
                enode * n        = get_enode(v);
                theory_var other = null_theory_var;
                TRACE("assume_eqs",
                      tout << "#" << n->get_owner_id() << " is_relevant_and_shared: " << is_relevant_and_shared(n) << "\n";);
                if (n != nullptr && is_relevant_and_shared(n)) {
                    other = table.insert_if_not_there(v);
                    if (other != v) {
                        enode * n2 = get_enode(other);
                        TRACE("assume_eqs", tout << "value(#" << n->get_owner_id() << ") = value(#" << n2->get_owner_id() << ")\n";);
                        if (assume_eq(n, n2)) {
                            TRACE("assume_eqs", tout << "new assumed eq\n";);
                            result = true;
                        }
                    }
                }
            }
            return result;
        }

        /**
           \brief When an eq atom n is created during the search, the default behavior is 
           to make sure that the n->get_arg(0)->get_id() < n->get_arg(1)->get_id().
           This may create some redundant atoms, since some theories/families use different
           conventions in their simplifiers. For example, arithmetic always force a numeral
           to be in the right hand side. So, this method should be redefined if the default
           behavior conflicts with a convention used by the theory/family.
           当一个等式原子n在搜索过程中被创造了，默认行为是确保n->get_arg(0)->get_id() < n->get_arg(1)->get_id()
           这可能产生一些多余的原子，因为一些理论会在他们的化简器中使用不同的转化。
           例如，算术理论总是强迫在右侧有一个数字。
           所以如果默认行为与理论使用的转化冲突时，该方法应该被重新定义
        */
        virtual app * mk_eq_atom(expr * lhs, expr * rhs) {
            ast_manager& m = get_manager();
            if (lhs->get_id() > rhs->get_id())
                std::swap(lhs, rhs);
            if (m.are_distinct(lhs, rhs))                
                return m.mk_false();
            if (m.are_equal(lhs, rhs))
                return m.mk_true();
            return get_manager().mk_eq(lhs, rhs);
        }

        literal mk_eq(expr * a, expr * b, bool gate_ctx);

        literal mk_preferred_eq(expr* a, expr* b);

        literal mk_literal(expr* e);

        enode* ensure_enode(expr* e);

        enode* get_root(expr* e) { return ensure_enode(e)->get_root(); }

        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------

        /**
           \brief Return true if theory support model construction
           如果理论支持模型构造则返回true
        */
        virtual bool build_models() const { 
            return true;
        }

        virtual void init_model(model_generator & m) {
        }

        virtual void finalize_model(model_generator & m) {
        }
        
        /**
           \brief Return a functor that can build the value (interpretation) for n.
           返回可以为n构造一个值（解释）的函数
        */
        virtual model_value_proc * mk_value(enode * n, model_generator & mg) {
            return nullptr;
        }

        virtual bool include_func_interp(func_decl* f) {
            return false;
        }

        // -----------------------------------
        //
        // Model checker
        //
        // -----------------------------------

        virtual bool get_value(enode * n, expr_ref & r) {
            return false;
        }

        virtual char const * get_name() const { return "unknown"; }

        // -----------------------------------
        //
        // Return a fresh new instance of the given theory.
        // This function is used to create a fresh context (new_ctx) containing the same theories of the context that owns this theory.
        //
        // We need the parameter new_ctx because of user_smt_theory :-(
        //返回一个给定理论的新例子，该函数用来构造一个新的context，包含了拥有该理论的context的相同理论
        // -----------------------------------
        virtual theory * mk_fresh(context * new_ctx) = 0;

    protected:
        // ----------------------------------------------------
        //
        // Auxiliary methods for assume_eqs
        //
        // smt::context is not defined at this point.
        //
        // ----------------------------------------------------

        bool is_relevant_and_shared(enode * n) const;

        bool assume_eq(enode * n1, enode * n2);
    };
    
};


