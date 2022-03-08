#include"nia_ls.h"
#include <sstream>
namespace nia{
//print
void ls_solver::print_formula(){
    for(int i=0;i<_num_clauses;i++){
        clause *cl=&(_clauses[i]);
        std::cout<<i<<"\n";
        for(int l_idx: cl->literals){
            std::cout<<l_idx<<": ";
            if(l_idx<0){std::cout<<"neg: ";}
            print_literal(_lits[std::abs(l_idx)]);}
        std::cout<<"\n";
    }
}

void ls_solver::print_formula_pbs(){
    std::cout<<"p wcnf "<<_num_vars<<" "<<(_num_lits-_num_vars*2)<<" "<<_num_vars+1<<"\n";
    for(int lit_idx=1;lit_idx<_num_lits;lit_idx++){
        lit *l=&(_lits[lit_idx]);
        if(l->pos_coff.size()==1&&l->neg_coff.size()==0&&l->pos_coff[0]==1&&l->key==-1){continue;}
        if(l->neg_coff.size()==1&&l->pos_coff.size()==0&&l->neg_coff[0]==1&&l->key==0){continue;}
        if(l->lits_index==0){continue;}
        print_lit_pbs(_lits[lit_idx]);
    }
    std::cout<<"2 0 1 1 0\n";
}

void ls_solver::print_formula_smt(){
    std::cout<<"(set-info :smt-lib-version 2.6)\n(set-logic QF_IDL)\n";
    for(variable &v:_vars){std::cout<<"(declare-fun "<<v.var_name<<" () "<<(v.is_nia?"Int":"Bool")<<")\n";}
    std::cout<<"(assert\n(and\n";
    for(clause &cl:_clauses){
        std::cout<<"(or ";
        for(int lit_idx:cl.literals){print_lit_smt(lit_idx);}
        std::cout<<")\n";
    }
    std::cout<<"))\n(check-sat)\n(exit)\n";
}


void ls_solver::print_term(term &t){
    for(int i=0;i<t.var_epxs.size();i++){
        var_exp * ve=&(t.var_epxs[i]);
        if(i!=0){std::cout<<"*";}
        std::cout<<_vars[ve->var_index].var_name;
        if(ve->exponent>1){std::cout<<"^"<<ve->exponent;}
    }
}
void ls_solver::print_literal(lit &l){
    if(!l.is_nia_lit){std::cout<<_vars[l.delta].var_name<<"\n";}
    else{
    for(int i=0;i<l.pos_coff.size();i++){
        std::cout<<"( "<<print_128(l.pos_coff[i])<<" * ";
        print_term(_terms[l.pos_coff_term_idx[i]]);
        std::cout<<" ) + ";
    }
    for(int i=0;i<l.neg_coff.size();i++){
        std::cout<<"( -"<<print_128(l.neg_coff[i])<<" * ";
        print_term(_terms[l.neg_coff_term_idx[i]]);
        std::cout<<" ) + ";
    }
    std::cout<<"( "<<print_128(l.key)<<" ) "<<(l.is_equal?"==":"<=")<<" 0\n";
    }
}

void ls_solver::print_lit_pbs(lit &l){
    __int128_t degree=l.key;
    for(int i=0;i<l.pos_coff.size();i++){degree+=l.pos_coff[i];}
    std::cout<<_num_vars+1<<" "<<print_128(degree)<<" ";
    for(int i=0;i<l.pos_coff.size();i++)
    {std::cout<<print_128(l.pos_coff[i])<<" "<<-(l.pos_coff_term_idx[i]+1)<<" ";}
    for(int i=0;i<l.neg_coff.size();i++)    {std::cout<<print_128(l.neg_coff[i])<<" "<<l.neg_coff_term_idx[i]+1<<" ";}
    std::cout<<"0\n";
}

void ls_solver::print_lit_smt(int lit_idx){
    lit *l=&(_lits[std::abs(lit_idx)]);
    if(l->is_nia_lit){
        std::cout<<"("<<(lit_idx>0?"<=":">")<<" (- "<<_vars[l->pos_coff_term_idx[0]].var_name<<" "<<_vars[l->neg_coff_term_idx[0]].var_name<<") "<<print_128(-l->key)<<" ) ";
    }
    else{
        if(lit_idx>0){std::cout<<_vars[l->delta].var_name<<" ";}
        else{std::cout<<"("<<" not "<<_vars[l->delta].var_name<<" ) ";}
    }
}

void ls_solver::print_mv(){
    std::cout<<"(model\n";
    for(uint64_t var_idx=0;var_idx<_num_vars;var_idx++){
        print_mv_vars(var_idx);
    }
    std::cout<<")\n";
}

void ls_solver::print_mv_vars(uint64_t var_idx){
    variable *v=&(_vars[var_idx]);
    __int128_t var_solution=_solution[var_idx];
    std::cout<<"  (define-fun "<<v->var_name<<" () ";
    if(v->is_nia){
        std::cout<<"Int ";
        if(var_solution>=0){std::cout<<print_128(var_solution)<<")\n";}
        else{std::cout<<"(- "<<print_128(-var_solution)<<"))\n";}
    }
    else{
        std::cout<<"Bool ";
        if(var_solution>0){std::cout<<"true )\n";}
        else{std::cout<<"false )\n";}
    }
}

void ls_solver::print_var_solution(std::string &var_name,std::string & var_value){
    uint64_t var_idx=0;
    if(name2tmp_var.find(var_name)==name2tmp_var.end()){
        var_value=print_128(0);
        return;
    }//Bool case: since the Bool var will directly enter resolution var
    //nia case follows
    int origin_var_idx=(int)name2tmp_var[var_name];
    if(name2var.find(var_name)!=name2var.end()){
        var_idx=name2var[var_name];
        var_value=print_128(_solution[var_idx]);
        return;
    }//the var exists in _vars
    else{
        var_value=print_128( _tmp_vars[origin_var_idx].low_bound);
        return;
    }//the var does not exist in reduced formula
}

std::string ls_solver::print_128(__int128_t n){
    std::stringstream ss;
    if (n==0) return "0";
        if (n<0) {
            ss<<"-";
            n=-n;
        }
        int a[50],ai=0;
        memset(a,0,sizeof a);
        while (n!=0){
            a[ai++]=n%10;
            n/=10;
        }
        for (int i=1;i<=ai;i++) ss<<abs(a[ai-i]);
        return ss.str();
}
}
