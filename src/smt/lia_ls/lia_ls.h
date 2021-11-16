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
#include "smt/lia_ls/lia_Array.h"

namespace lia {
const int max_int=2147483640;
//one arith lit is in the form of a_1*x_1+...+a_n*x_n+k<=0, the cofficient are divided into positive ones and negative ones, the coff are positive.
//if neg_coff =1 neg_coff_var=x pos_coff=1 pos_coff_var=y means y-x
struct lit{
    std::vector<int>            pos_coff_var_idx;
    std::vector<int>            pos_coff;
    std::vector<int>            neg_coff_var_idx;
    std::vector<int>            neg_coff;
    int                         key;
    int                         lits_index;
    int                         delta;//the current value of left side
};

struct variable{
    std::vector<int>            literals;
    std::vector<int>            literal_clause;//literal_clause[i]=c means the ith literal containing the var is in cth clause
    std::vector<int>            literal_coff;//literal_coff[i] denotes the coff of the var in corresponding literal
    std::vector<uint64_t>       clause_idxs;
    std::string                 var_name;
    int                         low_bound=-max_int;
    int                         upper_bound=max_int;
};

struct clause{
    std::vector<int>            literals;
    int                          weight=1;
    int                          sat_count;
};

class ls_solver{
public:
    
    //basic information
    uint64_t                    _num_vars;
    uint64_t                    _num_lits;
    uint64_t                    _num_clauses;
    uint64_t                    _num_opt=0;//the number of vars in all literals, which is the max number of operations
    std::vector<variable>       _vars;
    std::vector<variable>       _tmp_vars;
    std::vector<lit>            _lits;
    std::vector<int>            _bound_lits;//record the index of bounded lits
    std::vector<clause>         _clauses;
    Array                       *unsat_clauses;
    //solution
    std::vector<int>            _solution;
    std::vector<int>            _best_solutin;
    int                         best_found_cost;
    int                         best_found_this_restart;
    //control
    uint64_t                    _step;
    const uint64_t              _max_step;
    std::vector<uint64_t>       tabulist;//tabulist[2*var] and [2*var+1] means that var are forbidden to move forward or backward until then
    std::vector<int>            CClist;//CClist[2*var]==1 and [2*var+1]==1 means that var is allowed to move forward or backward
    int                          CC_mode;
    std::vector<uint64_t>       last_move;
    std::vector<int>            operation_var_idx_vec;
    std::vector<int>            operation_change_value_vec;
    std::chrono::steady_clock::time_point start;
    double                      best_cost_time;
    double                      _cutoff;
    std::mt19937                mt;
    const uint64_t              _additional_len;
    std::map<std::string,uint64_t> name2var;//map the name of a variable to its index
    // data structure for clause weighting
    const uint64_t              smooth_probability;
    uint64_t                    _swt_threshold;
    float                       _swt_p;//w=w*p+ave_w*(1-p)
    uint64_t                    total_clause_weight;
    
    //input transformation
    void                        split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern);
    void                        build_lits(std::string &in_string);
    void                        build_instance(std::vector<std::vector<int> >& clause_vec);
    uint64_t                    transfer_name_to_var(std::string & name);
    uint64_t                    transfer_name_to_tmp_var(std::string &name);
    void                        reduce_vars();//reduce the x-y in all lits to new var z
    
    
    //initialize
    ls_solver();
    ls_solver(int random_seed);
    void                        make_space();
    void                        make_lits_space(uint64_t num_lits){_num_lits=num_lits;_lits.resize(num_lits+_additional_len);};
    void                        initialize();
    void                        initialize_variable_datas();
    void                        initialize_lit_datas();
    void                        initialize_clause_datas();
    void                        build_neighbor();
    
    //random walk
    void                        update_clause_weight();
    void                        smooth_clause_weight();
    void                        random_walk();
    
    //construction
    void                        construct_slution_score();//construct the solution based on score
    uint64_t                    pick_construct_idx(int &best_value);
    void                        construct_move(uint64_t var_idx,int change_value);
    int                         construct_score(uint64_t var_idx,int change_value);
    
    //basic operations
    inline void                 sat_a_clause(uint64_t clause_idx){unsat_clauses->delete_element((int)clause_idx);};
    inline void                 unsat_a_clause(uint64_t clause_idx){unsat_clauses->insert_element((int)clause_idx);};
    bool                        update_best_solution();
    void                        modify_CC(uint64_t var_idx,int direction);
    int                         pick_critical_move(int &best_value);
    void                        critical_move(uint64_t var_idx,int change_value);
    void                        invert_lit(lit &l);
    int                         delta_lit(lit &l);
    double                      TimeElapsed();
    void                        clear_prev_data();
    int                         devide(int a, int b);
    void                        insert_operation(int var_idx,int change_value,int &operation_idx);
    //print
    void                        print_formula();
    void                        print_literal(lit &l);
    //calculate score
    int                         critical_score(uint64_t var_idx,int change_value);
    int                         critical_subscore(uint64_t var_idx,int change_value);
    void                        critical_score_subscore(uint64_t var_idx,int change_value);
    //check
    bool                        check_solution();

    //local search
    bool                        local_search();
};
}