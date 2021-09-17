#pragma once
#include <cstdio>
#include <chrono>
#include <string.h>
#include<stack>
#include<random>
#include<map>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdlib>
#include<exception>
#include<time.h>
#include<signal.h>
#include<unistd.h>
#include<sys/types.h>
#include<string>
#include "smt/idl_ls/idl_Array.h"

namespace boolidl {
//if is_idl_lit: _vars[prevar_idx]-_vars[posvar_idx]<=key
//else: if key>0: _vars[prevar_idx] else: neg(_vars[prevar_idx)
struct lit{
    uint64_t                    prevar_idx;
    uint64_t                    posvar_idx;
    int                         key;
    uint64_t                    clause_idx;
    bool                        is_idl_lit;
    int                         lits_index;//store the index in _lits, 0 means the lit is true or it has been deleted
};

struct variable{
    std::vector<lit>            literals;
    std::vector<uint64_t>       neighbor_var_idxs_idl;//idl vars in same clause
    std::vector<uint64_t>       neighbor_var_idxs_bool;//bool vars in same clause
    std::vector<uint64_t>       neighbor_var_idxs_in_lit;//vars in same lit
    std::vector<uint64_t>       clause_idxs;
    int                         score;// if it is a bool var, then the score is calculated beforehand
    std::string                 var_name;
    bool                        is_idl;
    bool                        is_delete=false;
    int up_bool=0;//the bool value of variables deleted(1 true -1 false)
};

struct clause{
    std::vector<lit>            literals;
    std::vector<lit>            idl_literals;
    std::vector<lit>            bool_literals;
    std::vector<uint64_t>       var_idxs;
    uint64_t                    sat_count;
    uint64_t                    weight;
    bool                        is_hard=true;
    lit                         watch_lit;//the lit with smallest delta
    lit                         last_true_lit;//the last true lit in a falsified clause
    int                         min_delta;
    bool                        is_delete=false;
};

class bool_ls_solver{
public:
    //basic informations and controls
    uint64_t                    _num_vars;
    uint64_t                    _num_bool_vars;
    uint64_t                    _num_idl_vars;
    uint64_t                    _num_lits;
    uint64_t                    _num_clauses;
    uint64_t                    _max_lit_num_in_clause=0;
    uint64_t                    _additional_len;
    int                         _random_seed=1;
    std::mt19937                mt;
    std::map<int64_t,uint64_t>  sym2var;
    std::map<int,uint64_t>      sym2bool_var;
    std::map<std::string,uint64_t> name2var;//map the name of a variable to its index
    double                      _cutoff;
    int64_t                     _average_k_value;
    uint64_t                    smooth_probability;
    uint64_t                    fix_0_var_idx;//the var is fixed to 0
    uint64_t                    _lit_in_unsast_clause_num;
    uint64_t                    _bool_lit_in_unsat_clause_num;
    std::vector<uint64_t>       tabulist;//tabulist[2*var] and [2*var+1] means that var are forbidden to move forward or backward until then, for bool vars, only tabulist[2*var] counts
    std::vector<int>            CClist;//CClist[2*var]==1 and [2*var+1]==1 means that var is allowed to move forward or backward, for bool vars, only CClist[2*var] counts
    std::vector<uint64_t>       last_move;
    std::vector<int>            operation_vec;
    std::vector<int>            operation_vec_idl;
    std::vector<int>            operation_vec_bool;
    std::vector<bool>           operation_is_last_true_vec;//for Novelty
    int                         h_inc;
    int                         CCmode=-1;//-1 means tabu; 0 means allowing the neighbor in clause; 1 means allowing the neighbor in lit (especially for idl); 2 means allowing opposite direction of neighbor in lit
    bool                        is_validation=false;
    uint64_t                    softclause_weight_threshold;

    //data structure
    std::vector<clause>         _clauses;
    std::stack<clause>           _reconstruct_stack;
    std::vector<variable>       _vars;
    std::vector<variable>       _resolution_vars;
    std::vector<lit>            _lits;
    std::vector<uint64_t>       _unsat_soft_clauses;
    std::vector<uint64_t>       _unsat_hard_clauses;
    std::vector<int64_t>        _index_in_unsat_soft_clauses;
    std::vector<int64_t>        _index_in_unsat_hard_clauses;
    //critical changing value
    std::vector<int>            _forward_critical_value;
    std::vector<int>            _backward_critical_value;
    //the clause with one sat number, and contains more than one lits
    Array                       *sat_num_one_clauses;
    //the idl_var and bool_var std::vector
    std::vector<uint64_t>       idl_var_vec;
    std::vector<uint64_t>       bool_var_vec;
    //to avoid choosing the same bool var
    std::vector<bool>           is_chosen_bool_var;
    int                         ref_zero=-1;//reference 0

    //solution information
    std::vector<int>            _solution;
    std::vector<int>            _best_solution;
    uint64_t                    _best_found_hard_cost;
    uint64_t                    _best_found_hard_cost_this_restart;
    uint64_t                    _best_found_soft_cost;
    double                      _best_cost_time;
    uint64_t                    _step;
    uint64_t                    _max_step;
    uint64_t                    _max_tries;

    // data structure for clause weighting
    uint64_t                    _swt_threshold;
    float                       _swt_p;//w=w*p+ave_w*(1-p)
    uint64_t                    total_clause_weight;

    std::chrono::steady_clock::time_point start;//time

    bool_ls_solver();
    bool                        parse_arguments(const int argc, char ** const argv);
    void                        split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern);
    void                        build_lits(std::string &in_string);
    bool                        build_instance(std::vector<std::vector<int> >& clause_vec);
    void                        up_bool_vars();
    bool                        local_search();
    void                        print_solution(bool detailed);
    void                        make_space();
    void                        make_lits_space(uint64_t num_lits){_num_lits=num_lits;_lits.resize(num_lits+_additional_len);};
    void                        build_neighbor_clausenum();
    inline  int64_t             get_cost();
    void                        print_formula();
    void                        print_literal(lit &l);
    uint64_t                    transfer_name_to_var(std::string & name,bool is_idl);
    uint64_t                    transfer_to_reduced_var(int v_idx);
    uint64_t                    transfer_to_reduced_bool_var(int v_idx);
    inline  void                invert_lit(lit &l);
    inline  int                 lit_delta(lit &l);
    void                        clear_prev_data();
    double                      TimeElapsed();
    //resolution
    void                        resolution();
    bool                        is_equal(lit &l1,lit & l2);
    bool                        is_neg(lit &l1,lit &l2);
    //unit prop
    void                        unit_prop();
    void                        reduce_clause();//reduce the deleted clauses and vars

    //main functions
    void                        initialize();
    void                        initialize_variable_datas();
    void                        initialize_clause_datas();
    void                        random_walk_all();
    void                        random_walk_all_bool();
    int64_t                     pick_critical_move(int64_t & direction);
    int64_t                     pick_critical_move_bool(int64_t & direction);
    void                        swap_from_small_weight_clause();
    void                        critical_move(uint64_t var_idx,uint64_t direction);
    void                        update_clause_weight();
    void                        update_clause_weight_critical();
    void                        smooth_clause_weight();
    void                        smooth_clause_weight_critical();
    
    //restart construction
    Array                        *unsat_clause_with_assigned_var;//unsat clause with at least one assigned var
    Array                        *cdcl_lit_with_assigned_var;//unsat cdcl lits with only one assigned var, pick critical move from this set
    Array                        *cdcl_lit_unsolved;//unsolved cdcl lits(unsolved->assigned_var->true/false)
    void                         record_cdcl_lits(std::vector<int> & cdcl_lits);
    std::vector<int>             var_is_assigned;//0 means the var is not assigned
    std::vector<int>             construct_unsat;//0 means the clause is unsat
    void                         construct_slution_score();//construct the solution based on score
    uint64_t                     pick_construct_idx(int &best_value);
    void                         construct_move(int var_idx,int value);
    int                          construct_score(int var_idx,int value);
    //functions for basic operations
    inline void                  sat_a_clause(uint64_t the_clause);
    inline void                  unsat_a_clause(uint64_t the_clause);
    bool                         update_best_solution();
    void                         hash_opt(int operation,int &var_idx,int &operation_direction,int &critical_value);
    void                         modifyCC(uint64_t var_idx,uint64_t direction);
    //calculate the score and subscore of a critical operation
    void                         critical_score_subscore(uint64_t var_idx,int change_value);
    int                          critical_score(uint64_t var_idx,int change_value,int &safety);//only calculate the score
    int                          critical_subscore(uint64_t var_idx,int change_value);//only calculate the subscore
    void                         add_swap_operation(int &operation_idx);// add swap operation from a random sat_num==1 clause
    bool                         check_solution();
    bool                         check_best_solution();
};
}