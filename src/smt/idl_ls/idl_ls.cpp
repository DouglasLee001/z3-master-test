#include "smt/idl_ls/idl_ls.h"
namespace boolidl{

bool_ls_solver::bool_ls_solver(){
    h_inc=1;
    softclause_weight_threshold=1;
    _additional_len=10;
    _max_tries=1;
    _max_step=UINT64_MAX;
    _swt_p=0.7;
    _swt_threshold=50;
    smooth_probability=3;
    _random_seed=1;
    mt.seed(_random_seed);
    _cutoff=600;
    CCmode=-1;
}
bool_ls_solver::bool_ls_solver(int random_seed){
    h_inc=1;
    softclause_weight_threshold=1;
    _additional_len=10;
    _max_tries=1;
    _max_step=UINT64_MAX;
    _swt_p=0.7;
    _swt_threshold=50;
    smooth_probability=3;
    _random_seed=random_seed;
    mt.seed(_random_seed);
    _cutoff=1200;
    CCmode=-1;
}

uint64_t bool_ls_solver::transfer_name_to_var(std::string & name,bool is_idl){
    if(name2var.find(name)==name2var.end()){
        name2var[name]=_resolution_vars.size();
        variable var;
        var.is_idl=is_idl;
        var.clause_idxs.reserve(64);
        var.var_name=name;
        _resolution_vars.push_back(var);
        if(is_idl){idl_var_vec.push_back(_resolution_vars.size()-1);}
        else{bool_var_vec.push_back(_resolution_vars.size()-1);}
        return _resolution_vars.size()-1;
    }
    else return name2var[name];
}

void bool_ls_solver::make_space(){
    _solution.resize(_num_vars+_additional_len);
    _best_solution.resize(_num_vars+_additional_len);
    _index_in_unsat_hard_clauses.resize(_num_clauses+_additional_len,-1);
    _index_in_unsat_soft_clauses.resize(_num_clauses+_additional_len,-1);
    tabulist.resize(2*_num_vars+_additional_len);
    CClist.resize(2*_num_vars+_additional_len);
    _forward_critical_value.resize(_num_vars+_additional_len);
    _backward_critical_value.resize(_num_vars+_additional_len);
    operation_vec.resize(_num_lits*2+_additional_len);
    operation_vec_idl.resize(_num_lits*2+_additional_len);
    operation_vec_bool.resize(_num_lits*2+_additional_len);
    operation_is_last_true_vec.resize(_num_lits*2+_additional_len);
    var_is_assigned.resize(_num_vars);
    unsat_clause_with_assigned_var=new Array((int)_num_clauses);
    construct_unsat.resize(_num_clauses);
    last_move.resize(_num_vars*2+_additional_len);
    sat_num_one_clauses=new Array((int)_num_clauses);
    cdcl_lit_with_assigned_var=new Array(2*(int)_num_lits+(int)_additional_len);
    cdcl_lit_unsolved=new Array(2*(int)_num_lits+(int)_additional_len);
    is_chosen_bool_var.resize(_num_vars+_additional_len,false);
    pure_bool_unsat_clauses=new Array((int)_num_clauses+(int)_additional_len);
    contain_bool_unsat_clauses=new Array((int)_num_clauses+(int)_additional_len);
    contain_idl_unsat_clauses=new Array((int)_num_clauses+(int)_additional_len);
}
/// build neighbor_var_idxs for each var
void bool_ls_solver::build_neighbor_clausenum(){
    uint64_t    j;
    uint64_t v, c;
    std::vector<char> neighbor_flag(_num_vars+_additional_len);
    std::vector<int64_t> clause_flag(_num_clauses+_additional_len);
    std::vector<int64_t> neighbor_in_lit_flag(_num_vars+_additional_len);
    for (j=0; j<neighbor_flag.size(); ++j ) {neighbor_flag[j] = 0;}
    for (j=0; j<neighbor_flag.size(); ++j ) {neighbor_in_lit_flag[j] = 0;}
    for (j=0;j<clause_flag.size();++j){clause_flag[j]=0;}
    for (v=0; v < _num_vars; ++v)
    {
        variable * vp = &(_vars[v]);
        for (lit lv : vp->literals)
        {
            if(lv.is_idl_lit){
            if(!neighbor_in_lit_flag[lv.prevar_idx]&&lv.prevar_idx!=v){
                neighbor_in_lit_flag[lv.prevar_idx]=1;
                vp->neighbor_var_idxs_in_lit.push_back(lv.prevar_idx);
            }
            if(!neighbor_in_lit_flag[lv.posvar_idx]&&lv.posvar_idx!=v){
                neighbor_in_lit_flag[lv.posvar_idx]=1;
                vp->neighbor_var_idxs_in_lit.push_back(lv.posvar_idx);
            }
            }
            c = lv.clause_idx;
            if (!clause_flag[c])
            {
                clause_flag[c] = 1;
                vp->clause_idxs.push_back(c);
                for (lit lc : _clauses[c].literals){
                    if(lc.is_idl_lit){//idl lit
                        if (!neighbor_flag[lc.prevar_idx] && lc.prevar_idx!=v){
                            neighbor_flag[lc.prevar_idx] = 1;
                            vp->neighbor_var_idxs_idl.push_back(lc.prevar_idx);
                        }
                        if (!neighbor_flag[lc.posvar_idx] && lc.posvar_idx!=v){
                            neighbor_flag[lc.posvar_idx] = 1;
                            vp->neighbor_var_idxs_idl.push_back(lc.posvar_idx);
                        }
                    }
                    else if (!neighbor_flag[lc.prevar_idx] && lc.prevar_idx!=v){//bool lit
                        neighbor_flag[lc.prevar_idx]=1;
                        vp->neighbor_var_idxs_bool.push_back(lc.prevar_idx);
                    }
                }
            }
        }
        for (uint64_t j:vp->neighbor_var_idxs_idl) {neighbor_flag[j] = 0;}
        for (uint64_t j:vp->neighbor_var_idxs_bool) {neighbor_flag[j]=0;}
        for (uint64_t j:vp->neighbor_var_idxs_in_lit) {neighbor_in_lit_flag[j] = 0;}
        for (j=0; j<vp->clause_idxs.size(); ++j) {clause_flag[vp->clause_idxs[j]] = 0;}
        for (j=0;j<vp->clause_idxs.size();++j){
            _clauses[vp->clause_idxs[j]].var_idxs.push_back(v);
        }
    }
}
void bool_ls_solver::split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern=" "){
    std::string::size_type pos;
    in_string+=pattern;
    size_t size=in_string.size();
    for(size_t i=0; i<size; i++){
    pos=in_string.find(pattern,i);
    if(pos<size){
        std::string s=in_string.substr(i,pos-i);
        str_vec.push_back(s);
        i=pos+pattern.size()-1;
        }
    }
}

void bool_ls_solver::build_lits(std::string & in_string){
    std::vector<std::string> vec;
    split_string(in_string, vec);
    if(vec[0]=="0"){_lits[0].lits_index=0; return;}
    int lit_index=std::atoi(vec[0].c_str());
    if(vec[1][1]=='!'){_lits[lit_index].lits_index=0;return;}//lits index==0 means that the lit is true
    uint64_t pos,pre;
    int k;
    lit l;
    if(vec[1]=="or"){
        l.prevar_idx=transfer_name_to_var(vec[2], false);
        l.key=1;
        l.is_idl_lit=false;
        l.lits_index=lit_index;
        _lits[lit_index]=l;
        return;
    }//or term in the form: 1 or newvar_2
    if(vec.size()>2){
        if(vec.size()>6){
            k=std::atoi(vec[12].c_str());
            pos=transfer_name_to_var(vec[9],true);
            pre=transfer_name_to_var(vec[5],true);
        }
        else{
            k=std::atoi(vec[4].c_str());
            std::string ref_zero="__ref__zero__";
            pos=transfer_name_to_var(ref_zero, true);
            pre=transfer_name_to_var(vec[3], true);
        }
        if(vec[2]==">="){std::swap(pre, pos);k=-k;}
        l.prevar_idx=pre;l.posvar_idx=pos;l.key=k;l.is_idl_lit=true;
    }//idl lit
    else{
        l.prevar_idx=transfer_name_to_var(vec[1], false);
        l.key=1;
        l.is_idl_lit=false;
    }//boolean lit
    l.lits_index=lit_index;
    _lits[lit_index]=l;
}

bool bool_ls_solver::build_instance(std::vector<std::vector<int> >& clause_vec){
    _average_k_value=0;
    int num_idl_lit=0;
    _clauses.reserve(clause_vec.size());
    for (auto clause_curr:clause_vec) {
        clause cur_clause;
        bool is_tautology=false;
        for (auto l_idx : clause_curr) {if(_lits[std::abs(l_idx)].lits_index==0){is_tautology=true;break;}}
        if(is_tautology){continue;}
        for (auto l_idx : clause_curr) {
            if(l_idx==0){is_tautology=true;break;}
            lit curlit;
            if(l_idx<0){curlit=_lits[-l_idx];invert_lit(curlit);}
            else{curlit=_lits[l_idx];}
            if(curlit.is_idl_lit){
                num_idl_lit++;
                _average_k_value+=abs(curlit.key);
            }
            else{_resolution_vars[curlit.prevar_idx].clause_idxs.push_back(_clauses.size());}
            cur_clause.literals.push_back(curlit);
            cur_clause.is_hard=true;
            cur_clause.weight=1;
        }
        _clauses.push_back(cur_clause);
    }
    _num_clauses=_clauses.size();
    unit_prop();
    resolution();
    unit_prop();
    reduce_clause();
//    print_formula();
//    std::cout<<"bool var num: "<<bool_var_vec.size()<<"\n";
    _num_clauses=_clauses.size();
    _num_vars=_vars.size();
    _num_bool_vars=bool_var_vec.size();
    _num_idl_vars=idl_var_vec.size();
    total_clause_weight=_num_clauses;
    make_space();
    build_neighbor_clausenum();
    if(num_idl_lit>0){_average_k_value/=num_idl_lit;}
    if(_average_k_value<1)_average_k_value=1;
    _best_found_hard_cost=_num_clauses;
    _best_found_soft_cost=0;
    return true;
}
//resolution
void bool_ls_solver::resolution(){
    std::vector<uint64_t> pos_clauses(10*_num_clauses);
    std::vector<uint64_t> neg_clauses(10*_num_clauses);
    int pos_clause_size,neg_clause_size;
    bool is_improve=true;
    while(is_improve){
        is_improve=false;
    for(uint64_t bool_var_idx:bool_var_vec){
        if(_resolution_vars[bool_var_idx].is_delete)continue;
        pos_clause_size=0;neg_clause_size=0;
        for(int i=0;i<_resolution_vars[bool_var_idx].clause_idxs.size();i++){
            uint64_t clause_idx=_resolution_vars[bool_var_idx].clause_idxs[i];
            if(_clauses[clause_idx].is_delete)continue;
            for(lit l:_clauses[clause_idx].literals){
                if(l.prevar_idx==bool_var_idx){
                    if(l.key>0){pos_clauses[pos_clause_size++]=clause_idx;}
                    else{neg_clauses[neg_clause_size++]=clause_idx;}
                    break;
                }
            }
        }//determine the pos_clause and neg_clause
        int tautology_num=0;
        for(int i=0;i<pos_clause_size;i++){//pos clause X neg clause
            uint64_t pos_clause_idx=pos_clauses[i];
            for(int j=0;j<neg_clause_size;j++){
                uint64_t neg_clause_idx=neg_clauses[j];
                for(int k=0;k<_clauses[neg_clause_idx].literals.size();k++){
                    lit l=_clauses[neg_clause_idx].literals[k];
                    if(l.prevar_idx!=bool_var_idx){//the bool_var for resolution is not considered
                        for(uint64_t x=0;x<_clauses[pos_clause_idx].literals.size();x++){
                            if(is_neg(l, _clauses[pos_clause_idx].literals[x])){
                                tautology_num++;
                                break;
                            }//if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                    }
                }
            }
        }
        if((pos_clause_size*neg_clause_size-tautology_num)>(pos_clause_size+neg_clause_size)){continue;}//if deleting the var can cause 2 times clauses, then skip it
        for(uint64_t clause_idx:_resolution_vars[bool_var_idx].clause_idxs){//delete the clauses of bool_var
            _clauses[clause_idx].is_delete=true;
            for(lit l:_clauses[clause_idx].literals){//delete the clause from corresponding bool var
                if(!l.is_idl_lit&&l.prevar_idx!=bool_var_idx){
                    uint64_t delete_idx=0;
                    for(;delete_idx<_resolution_vars[l.prevar_idx].clause_idxs.size();delete_idx++){
                        if(_resolution_vars[l.prevar_idx].clause_idxs[delete_idx]==clause_idx){
                            _resolution_vars[l.prevar_idx].clause_idxs[delete_idx]=_resolution_vars[l.prevar_idx].clause_idxs.back();
                            _resolution_vars[l.prevar_idx].clause_idxs.pop_back();
                            break;
                        }
                    }
                }
            }
        }
        is_improve=true;
        _resolution_vars[bool_var_idx].is_delete=true;
        if(pos_clause_size==0){_resolution_vars[bool_var_idx].up_bool=-1;}//if it is a false pure lit, the var is set to false
        if(neg_clause_size==0){_resolution_vars[bool_var_idx].up_bool=1;}//if it is a true pure lit, the var is set to true
        if(pos_clause_size==0||neg_clause_size==0)continue;//pos or neg clause is empty, meaning the clauses are SAT when assigned to true or false, then cannot resolute, just delete the clause
        for(int i=0;i<pos_clause_size;i++){//pos clause X neg clause
            uint64_t pos_clause_idx=pos_clauses[i];
            for(int j=0;j<neg_clause_size;j++){
                uint64_t neg_clause_idx=neg_clauses[j];
                clause new_clause;
                uint64_t pos_lit_size=_clauses[pos_clause_idx].literals.size();
                uint64_t neg_lit_size=_clauses[neg_clause_idx].literals.size();
                new_clause.literals.reserve(pos_lit_size+neg_lit_size);
                bool is_tautology=false;
                for(int k=0;k<pos_lit_size;k++){
                    lit l=_clauses[pos_clause_idx].literals[k];
                    if(l.prevar_idx!=bool_var_idx){new_clause.literals.push_back(l);}
                }//add the lits in pos clause to new clause
                for(int k=0;k<neg_lit_size;k++){
                    lit l=_clauses[neg_clause_idx].literals[k];
                    if(l.prevar_idx!=bool_var_idx){
                        bool is_existed_lit=false;
                        for(uint64_t i=0;i<pos_lit_size-1;i++){
                            if(is_equal(l, new_clause.literals[i])){is_existed_lit=true;break;}// if the lit has existed, then it will not be added
                            if(is_neg(l, new_clause.literals[i])){is_tautology=true;break;}//if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                        if(is_tautology){break;}
                        if(!is_existed_lit){new_clause.literals.push_back(l);}
                    }
                }
                if(!is_tautology){//add new clause, and modify the clause of corresponding bool var
                    for(lit l:new_clause.literals){
                        if(!l.is_idl_lit){
                            _resolution_vars[l.prevar_idx].clause_idxs.push_back((int)_num_clauses);
                        }
                    }
                    _clauses.push_back(new_clause);
                    _num_clauses++;
                }
            }
        }
        for(int i=0;i<pos_clause_size;i++){
            clause pos_cl=_clauses[pos_clauses[i]];
            for(int j=0;j<pos_cl.literals.size();j++){
                if(pos_cl.literals[j].prevar_idx==bool_var_idx){
                    lit tmp=pos_cl.literals[j];
                    pos_cl.literals[j]=pos_cl.literals[0];
                    pos_cl.literals[0]=tmp;
                    break;
                }
            }
            _reconstruct_stack.push(pos_cl);
        }
        for(int i=0;i<neg_clause_size;i++){
            clause neg_cl=_clauses[neg_clauses[i]];
            for(int j=0;j<neg_cl.literals.size();j++){
                if(neg_cl.literals[j].prevar_idx==bool_var_idx){
                    lit tmp=neg_cl.literals[j];
                    neg_cl.literals[j]=neg_cl.literals[0];
                    neg_cl.literals[0]=tmp;
                    break;
                }
            }
            _reconstruct_stack.push(neg_cl);
        }
    }
    }
}
void bool_ls_solver::up_bool_vars(){//reconstruct the solution by pop the stack
    for(int i=0;i<_resolution_vars.size();i++){if(!_resolution_vars[i].is_idl&&_resolution_vars[i].up_bool==0){_resolution_vars[i].up_bool=-1;}}//set all origin bool var as false
    while(!_reconstruct_stack.empty()){
        clause cl=_reconstruct_stack.top();
        _reconstruct_stack.pop();
        bool sat_flag=false;
        for(lit l:cl.literals){
            if(l.is_idl_lit){
                if(sym2var.find(l.prevar_idx)==sym2var.end()||sym2var.find(l.posvar_idx)==sym2var.end()){sat_flag=true;break;}
                else if(_best_solution[sym2var[l.prevar_idx]]-_best_solution[sym2var[l.posvar_idx]]<=l.key){sat_flag=true;break;}
            }
            else{
                if(sym2bool_var.find((int)l.prevar_idx)==sym2bool_var.end()){
                    if((l.key>0&&_resolution_vars[l.prevar_idx].up_bool>0)||(l.key<0&&_resolution_vars[l.prevar_idx].up_bool<0)){sat_flag=true;break;}}
                else if((_best_solution[sym2bool_var[(int)l.prevar_idx]]>0&&l.key>0)||(_best_solution[sym2bool_var[(int)l.prevar_idx]]<0&&l.key<0)){sat_flag=true;break;}
            }
        }
        if(sat_flag==false){_resolution_vars[cl.literals[0].prevar_idx].up_bool=1;}//if the clause is false, flip the var
    }
}

void bool_ls_solver::unit_prop(){
    std::stack<uint64_t> unit_clause;//the var_idx in the unit clause
    for(uint64_t clause_idx=0;clause_idx<_num_clauses;clause_idx++){//the unit clause is the undeleted clause containing only one bool var
        if(!_clauses[clause_idx].is_delete&&_clauses[clause_idx].literals.size()==1&&!_clauses[clause_idx].literals[0].is_idl_lit){unit_clause.push(clause_idx);}
    }
    while(!unit_clause.empty()){
        uint64_t unit_clause_idx=unit_clause.top();
        unit_clause.pop();
        if(_clauses[unit_clause_idx].is_delete){continue;}
        int is_pos_lit=_clauses[unit_clause_idx].literals[0].key;
        uint64_t unit_var=_clauses[unit_clause_idx].literals[0].prevar_idx;
        _resolution_vars[unit_var].up_bool=is_pos_lit;//set the solution of a boolean var as its unit propogation value
        _resolution_vars[unit_var].is_delete=true;
        for(uint64_t cl_idx:_resolution_vars[unit_var].clause_idxs){
            clause *cl=&(_clauses[cl_idx]);
            if(cl->is_delete)continue;
            for(uint64_t lit_idx=0;lit_idx<cl->literals.size();lit_idx++){
                lit l=cl->literals[lit_idx];
                if(!l.is_idl_lit&&l.prevar_idx==unit_var){
                    if((is_pos_lit>0&&l.key>0)||(is_pos_lit<0&&l.key<0)){
                        cl->is_delete=true;
                        for(lit l:cl->literals){//delete the clause from corresponding bool var
                            if(!l.is_idl_lit&&l.prevar_idx!=unit_var){
                                for(uint64_t delete_idx=0;delete_idx<_resolution_vars[l.prevar_idx].clause_idxs.size();delete_idx++){
                                    if(_resolution_vars[l.prevar_idx].clause_idxs[delete_idx]==cl_idx){
                                        _resolution_vars[l.prevar_idx].clause_idxs[delete_idx]=_resolution_vars[l.prevar_idx].clause_idxs.back();
                                        _resolution_vars[l.prevar_idx].clause_idxs.pop_back();
                                        break;
                                    }
                                }
                            }
                        }
                    }//if there exist same lit, the clause is already set true
                    else{//else delete the lit
                        cl->literals[lit_idx]=cl->literals.back();
                        cl->literals.pop_back();
                        if(cl->literals.size()==1&&!cl->literals[0].is_idl_lit){unit_clause.push(cl_idx);}//if after deleting, it becomes unit clause
                    }
                    break;
                }
            }
        }
    }
}
void bool_ls_solver::reduce_clause(){
    sym2var.clear();
    sym2bool_var.clear();
    bool_var_vec.clear();
    idl_var_vec.clear();
    _vars.reserve(_resolution_vars.size());
    int i,reduced_clause_num;
    i=0;reduced_clause_num=0;
    for(;i<_num_clauses;i++){if(!_clauses[i].is_delete){_clauses[reduced_clause_num++]=_clauses[i];}}
    _clauses.resize(reduced_clause_num);
    for(i=0;i<reduced_clause_num;i++){
        _clauses[i].weight=1;
        for(int k=0;k<_clauses[i].literals.size();k++){
            lit *l=&(_clauses[i].literals[k]);
            l->clause_idx=i;
            if(l->is_idl_lit){
                _clauses[i].is_pure_boolean=false;//当出现了一个整数文字，意味着该子句不是纯bool
                l->prevar_idx=transfer_to_reduced_var((int)l->prevar_idx);
                l->posvar_idx=transfer_to_reduced_var((int)l->posvar_idx);
                _vars[l->prevar_idx].literals.push_back(*l);
                _vars[l->posvar_idx].literals.push_back(*l);
                _clauses[i].idl_literals.push_back(*l);
            }
            else{
                l->prevar_idx=transfer_to_reduced_bool_var((int)l->prevar_idx);
                _vars[l->prevar_idx].literals.push_back(*l);
                _clauses[i].bool_literals.push_back(*l);
            }
        }
    }
    _vars.resize(_vars.size());
    _num_idl_lits=0;_num_bool_lits=0;
    for(lit &l:_lits){
        if(l.is_idl_lit){
            if(sym2var.find(l.prevar_idx)!=sym2var.end()&&sym2var.find(l.posvar_idx)!=sym2var.end()){
                l.prevar_idx=sym2var[(int)l.prevar_idx];
                l.posvar_idx=sym2var[(int)l.posvar_idx];
                _num_idl_lits++;
            }
            else{l.lits_index=0;}
        }
        else{
            if(sym2bool_var.find((int)l.prevar_idx)!=sym2bool_var.end()){
                l.prevar_idx=sym2bool_var[(int)l.prevar_idx];
                _num_bool_lits++;
            }
            else{l.lits_index=0;}
        }
    }//map term in lits to _vars, the lits_index of those lits with vars deleted are set as 0, indicating that they are deleted
    uint64_t max_lit_num=0;
    for(auto var_idx:idl_var_vec){
        if(_vars[var_idx].literals.size()>max_lit_num){
            idl_var_idx_with_most_lits=var_idx;
            max_lit_num=_vars[var_idx].literals.size();
        }
    }
}
uint64_t bool_ls_solver::transfer_to_reduced_var(int v_idx){
    if(sym2var.find(v_idx)==sym2var.end()){
        sym2var[v_idx]=_vars.size();
        variable var;
        var.is_idl=true;
        var.var_name=_resolution_vars[v_idx].var_name;
        _vars.push_back(var);
        idl_var_vec.push_back(_vars.size()-1);
        return _vars.size()-1;
    }
    else return sym2var[v_idx];
}
uint64_t bool_ls_solver::transfer_to_reduced_bool_var(int v_idx){
    if(sym2bool_var.find(v_idx)==sym2bool_var.end()){
        sym2bool_var[v_idx]=_vars.size();
        variable var;
        var.is_idl=false;
        var.var_name=_resolution_vars[v_idx].var_name;
        _vars.push_back(var);
        bool_var_vec.push_back(_vars.size()-1);
        return _vars.size()-1;
    }
    else return sym2bool_var[v_idx];
}
/**********lit equal or neg***********/
bool bool_ls_solver::is_equal(lit &l1, lit &l2){
    if(l1.is_idl_lit&&l2.is_idl_lit){return l1.prevar_idx==l2.prevar_idx&&l1.posvar_idx==l2.posvar_idx&&l2.posvar_idx&&l1.key==l2.key;}
    else if(!l1.is_idl_lit&&!l2.is_idl_lit){return (l1.prevar_idx==l2.prevar_idx)&&((l1.key>0&&l2.key>0)||(l1.key<0&&l2.key<0));}
    return false;
}
bool bool_ls_solver::is_neg(lit &l1, lit &l2){
    if(l1.is_idl_lit&&l2.is_idl_lit){return l1.prevar_idx==l2.posvar_idx&&l1.posvar_idx==l2.prevar_idx&&(l1.key==(-1-l2.key));}
    else if(!l1.is_idl_lit&&!l2.is_idl_lit){return (l1.prevar_idx==l2.prevar_idx)&&((l1.key>0&&l2.key<0)||(l1.key<0&&l2.key>0));}
    return false;
}


void bool_ls_solver::clear_prev_data(){
    for(uint64_t v:bool_var_vec){_vars[v].score=0;}
}
/************initialization**************/

void bool_ls_solver::initialize_variable_datas(){
    
    //last move step
    for(uint64_t i=0;i<_num_vars;i++){last_move[2*i]=last_move[2*i+1]=0;}
    //tabulist
    for(uint64_t i=0;i<_num_vars;i++){tabulist[2*i]=tabulist[2*i+1]=0;}
    //CClist
    for (uint64_t i=0;i<_num_vars;i++){CClist[2*i]=CClist[2*i+1]=1;}
}

void bool_ls_solver::initialize_clause_datas(){
    _lit_in_unsast_clause_num=0;
    _bool_lit_in_unsat_clause_num=0;
    for(uint64_t c=0;c<_num_clauses;c++){
        _clauses[c].sat_count=0;
        _clauses[c].weight=1;
        _clauses[c].min_delta=INT32_MAX;
        _clauses[c].last_true_lit.prevar_idx=-1;
        for(lit l:_clauses[c].literals){
            int delta=lit_delta(l);
            if(delta<=0){
                _clauses[c].sat_count++;
                delta=0;
            }
            if(delta<_clauses[c].min_delta){
                _clauses[c].min_delta=delta;
                _clauses[c].watch_lit=l;
            }
        }
        if(_clauses[c].sat_count==0){
            unsat_a_clause(c);
            _lit_in_unsast_clause_num+=_clauses[c].literals.size();
            _bool_lit_in_unsat_clause_num+=_clauses[c].bool_literals.size();
            for(lit &bl:_clauses[c].bool_literals){_vars[bl.prevar_idx].score++;}
        }
        else{sat_a_clause(c);}
        if(_clauses[c].sat_count==1){sat_num_one_clauses->insert_element((int)c);
            if(!_clauses[c].watch_lit.is_idl_lit){_vars[_clauses[c].watch_lit.prevar_idx].score--;}}
        else{sat_num_one_clauses->delete_element((int)c);}
    }
    total_clause_weight=_num_clauses;
}

void bool_ls_solver::initialize(){
    clear_prev_data();
    construct_slution_score();
    initialize_clause_datas();
    initialize_variable_datas();
    _best_found_hard_cost_this_restart=_unsat_hard_clauses.size();
    update_best_solution();
}

/**********restart construction***********/
void bool_ls_solver::record_cdcl_lits(std::vector<int> & cdcl_lits){
    _num_cdcl_idl_lits=0;
    _num_cdcl_bool_lits=0;
    cdcl_lit_with_assigned_var->clear();
    cdcl_lit_unsolved->clear();
    for(int l:cdcl_lits){
        if(l>=(int)_num_lits||l<=-(int)_num_lits){continue;}//those outside the _lits are ignored
        lit* l_curr=&(_lits[std::abs(l)]);
        if(l_curr->lits_index!=0){
            cdcl_lit_unsolved->insert_element(l+(int)_num_lits);
            if(l_curr->is_idl_lit){_num_cdcl_idl_lits++;}
            else{_num_cdcl_bool_lits++;}
        }
    }//in order to make sure that elements inserted are non-negative
}

void bool_ls_solver::construct_slution_score(){
    fill(var_is_assigned.begin(), var_is_assigned.end(), 0);
    fill(construct_unsat.begin(), construct_unsat.end(), 0);
    unsat_clause_with_assigned_var->clear();
    std::vector<int> cdcl_bool_lits_assignment;
    cdcl_bool_lits_assignment.reserve(_num_cdcl_bool_lits+_additional_len);
    for(int i=0;i<cdcl_lit_unsolved->size();i++){
        int lit_idx=cdcl_lit_unsolved->element_at(i)-(int)_num_lits;//the cdcl lit assignment
        if(!_lits[std::abs(lit_idx)].is_idl_lit){cdcl_bool_lits_assignment.push_back(lit_idx);}//record those boolean cdcl lit assignment
    }
    for(int i=0;i<cdcl_bool_lits_assignment.size();i++){
        int lit_idx=cdcl_bool_lits_assignment[i];
        int best_value=(lit_idx>0)?1:(-1);
        int var_idx=(int)_lits[std::abs(lit_idx)].prevar_idx;
        construct_move(var_idx, best_value);//make the contruct move
    }//first assign the boolean var of cdcl value
    uint64_t var_idx=idl_var_vec[mt()%idl_var_vec.size()];//first choose an idl var, assign it to 0
    int     best_value=0;
    var_is_assigned[var_idx]=1;
    _solution[var_idx]=best_value;
    for(uint64_t i: _vars[var_idx].clause_idxs){unsat_clause_with_assigned_var->insert_element(int (i));}
    for(lit l:_vars[var_idx].literals){
        int l_idx=l.lits_index+(int)_num_lits;
        int neg_l_idx=-l.lits_index+(int)_num_lits;
        if(cdcl_lit_unsolved->is_in_array(l_idx)){cdcl_lit_unsolved->delete_element(l_idx);cdcl_lit_with_assigned_var->insert_element(l_idx);}//transfer the lit from unsolved to assigned var
        else if(cdcl_lit_unsolved->is_in_array(neg_l_idx)){cdcl_lit_unsolved->delete_element(neg_l_idx);cdcl_lit_with_assigned_var->insert_element(neg_l_idx);}
    }
    for(uint64_t i=1+cdcl_bool_lits_assignment.size();i<_num_vars;i++){
        var_idx=pick_construct_idx(best_value);
        construct_move((int)var_idx, best_value);
    }
}

uint64_t bool_ls_solver::pick_construct_idx(int &best_value){
    int best_score,score,cnt,value,direction,var_idx;
    uint64_t    best_var_idx=0;
    best_score=INT32_MIN;
    best_value=0;
    int operation_idx=0;
    for(int i=0;i<cdcl_lit_with_assigned_var->size();i++){
        int l_index=cdcl_lit_with_assigned_var->element_at(i)-(int)_num_lits;//l_index is the index of lit (maybe negative)
        lit l=_lits[std::abs(l_index)];
        if(l_index<0){invert_lit(l);}//l is the corresponding lit
        if(l.is_idl_lit){
            if(var_is_assigned[l.prevar_idx]==0&&var_is_assigned[l.posvar_idx]){operation_vec[operation_idx++]=(l.key+_solution[l.posvar_idx])*(int)_num_vars+(int)l.prevar_idx;}
            else if(var_is_assigned[l.posvar_idx]==0&&var_is_assigned[l.prevar_idx]==1){operation_vec[operation_idx++]=(-l.key+_solution[l.prevar_idx])*(int)_num_vars+(int)l.posvar_idx;}
        }//no need to handle the boolean var, since they are assigned as the cdcl lits before construction
    }
    for(int i=0;i<unsat_clause_with_assigned_var->size();i++){
        clause *cl=&(_clauses[unsat_clause_with_assigned_var->element_at(i)]);
        for(lit l:cl->literals){
            if(l.is_idl_lit){
            //one var is assigned while the other is not
            if(var_is_assigned[l.prevar_idx]==0&&var_is_assigned[l.posvar_idx]==1){
                var_idx=(int)l.prevar_idx;
                value=l.key+_solution[l.posvar_idx];
                operation_vec[operation_idx++]=value*(int)_num_vars+var_idx;
            }
            if(var_is_assigned[l.posvar_idx]==0&&var_is_assigned[l.prevar_idx]==1){
                var_idx=(int)l.posvar_idx;
                value=-l.key+_solution[l.prevar_idx];
                operation_vec[operation_idx++]=value*(int)_num_vars+var_idx;
            }
            }
            else if(var_is_assigned[l.prevar_idx]==0){
                value=(l.key>0)?1:-1;
                var_idx=(int)l.prevar_idx;
                operation_vec[operation_idx++]=value*(int)_num_vars+var_idx;
            }
        }
    }
    std::shuffle(operation_vec.begin(), operation_vec.begin()+operation_idx, mt);
    cnt=std::min(45,operation_idx);
    for(int i=0;i<cnt;i++){
        hash_opt(operation_vec[i], var_idx, direction, value);
        score=construct_score(var_idx, value);
        if(score>best_score){
            best_score=score;
            best_var_idx=var_idx;
            best_value=value;
        }
    }
    //if there is no operation, choose a random unassigned var and assign it randomly
    if(cnt==0){
        int i=0;
        for(;i<_num_vars;i++){if(var_is_assigned[i]==0){best_var_idx=i; break;}}
        if(_vars[i].is_idl){best_value=mt()%_average_k_value;}
        else{best_value=(mt()%2==0)?1:-1;}
    }
    return best_var_idx;
}

int bool_ls_solver::construct_score(int var_idx, int value){
    int score=0;
    variable *var=&(_vars[var_idx]);
    if(var->is_idl){
    uint64_t last_sat_clause_idx=UINT64_MAX;
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        // the clause is sat
        if(l.clause_idx==last_sat_clause_idx||construct_unsat[l.clause_idx]==1){
            last_sat_clause_idx=l.clause_idx;
            continue;
        }
        if( ((int)l.posvar_idx==var_idx&&var_is_assigned[l.prevar_idx]==1&&(value>=(_solution[l.prevar_idx]-l.key)))||
            ((int)l.prevar_idx==var_idx&&var_is_assigned[l.posvar_idx]==1&&(value<=(_solution[l.posvar_idx]+l.key))) ){
            // score++;
           score+=_clauses[l.clause_idx].weight;
            last_sat_clause_idx=l.clause_idx;
        }
    }
        for(lit l:var->literals){
            int l_idx=l.lits_index+(int)_num_lits;
            int neg_l_idx=(-l.lits_index)+(int)_num_lits;
            if((!cdcl_lit_with_assigned_var->is_in_array(l_idx))&&(!cdcl_lit_with_assigned_var->is_in_array(neg_l_idx))){continue;}//the assignment will not affect the truth of cdcl lit
            bool is_in_cdcl,mk_true;
            is_in_cdcl=cdcl_lit_with_assigned_var->is_in_array(l_idx);//this lit(neg) is in cdcl
            mk_true=(((int)l.posvar_idx==var_idx&&(value>=(_solution[l.prevar_idx]-l.key))) || ((int)l.prevar_idx==var_idx&&(value<=(_solution[l.posvar_idx]+l.key))) );//this lit can be made true(false)
            if(is_in_cdcl==mk_true){score+=10;}//the lit and its neg cannot appear simultaneously, since that is boolean inconsistent
            else{score-=10;}
        }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(construct_unsat[l.clause_idx]==1) {continue;}
            else if((l.key>0&&value>0)||(l.key<0&&value<0)) {score+=_clauses[l.clause_idx].weight;}
        }
    }
    return score;
}

//set solution[var_idx] to value
void bool_ls_solver::construct_move(int var_idx, int value){
    variable *var=&(_vars[var_idx]);
    if(var->is_idl){
    uint64_t last_sat_clause_idx=UINT64_MAX;
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        // the clause is sat
        if(l.clause_idx==last_sat_clause_idx||construct_unsat[l.clause_idx]==1){
            last_sat_clause_idx=l.clause_idx;
            continue;
        }
        if( ((int)l.posvar_idx==var_idx&&var_is_assigned[l.prevar_idx]==1&&(value>=(_solution[l.prevar_idx]-l.key)))||
            ((int)l.prevar_idx==var_idx&&var_is_assigned[l.posvar_idx]==1&&(value<=(_solution[l.posvar_idx]+l.key))) ){
            construct_unsat[l.clause_idx]=1;
            last_sat_clause_idx=l.clause_idx;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if((l.key>0&&value>0)||(l.key<0&&value<0)){construct_unsat[l.clause_idx]=1;}
        }
    }
    for(uint64_t clause_idx:_vars[var_idx].clause_idxs){
        if(construct_unsat[clause_idx]==0){unsat_clause_with_assigned_var->insert_element((int)clause_idx);}
        else{unsat_clause_with_assigned_var->delete_element((int)clause_idx);}
    }
    if(var->is_idl){
        for(lit l:_vars[var_idx].literals){
            int l_idx=l.lits_index+(int)_num_lits;
            int neg_l_idx=-l.lits_index+(int)_num_lits;
            if(cdcl_lit_unsolved->is_in_array(l_idx)){cdcl_lit_unsolved->delete_element(l_idx);cdcl_lit_with_assigned_var->insert_element(l_idx);}
            else if(cdcl_lit_unsolved->is_in_array(neg_l_idx)){cdcl_lit_unsolved->delete_element(neg_l_idx);cdcl_lit_with_assigned_var->insert_element(neg_l_idx);}//assign the first var in cdcl lit
            else if(cdcl_lit_with_assigned_var->is_in_array(l_idx)){cdcl_lit_with_assigned_var->delete_element(l_idx);}
            else if(cdcl_lit_with_assigned_var->is_in_array(neg_l_idx)){cdcl_lit_with_assigned_var->delete_element(neg_l_idx);}//assign the second var in cdcl lit
        }
    }
    else{
        lit l=_vars[var_idx].literals[0];//remove the lits and neg lits of assigned boolean var from cdcl_lit_unsolved
        cdcl_lit_unsolved->delete_element(l.lits_index+(int)_num_lits);
        cdcl_lit_unsolved->delete_element(-l.lits_index+(int)_num_lits);
    }
    _solution[var_idx]=value;
    var_is_assigned[var_idx]=1;
}

/**********sat or unsat a clause***********/
void bool_ls_solver::unsat_a_clause(uint64_t the_clause){
    if(_clauses[the_clause].is_hard==true&&_index_in_unsat_hard_clauses[the_clause]==-1){
        _index_in_unsat_hard_clauses[the_clause]=_unsat_hard_clauses.size();
        _unsat_hard_clauses.push_back(the_clause);
    }
    else if(_clauses[the_clause].is_hard==false&&_index_in_unsat_soft_clauses[the_clause]==-1){
        _index_in_unsat_soft_clauses[the_clause]=_unsat_soft_clauses.size();
        _unsat_soft_clauses.push_back(the_clause);
    }
    if(_clauses[the_clause].is_pure_boolean){pure_bool_unsat_clauses->insert_element((int)the_clause);}//如果该子句是纯布尔子句，则将其加入纯bool假子句
    if(_clauses[the_clause].bool_literals.size()>0){contain_bool_unsat_clauses->insert_element((int)the_clause);}
    if(_clauses[the_clause].idl_literals.size()>0){contain_idl_unsat_clauses->insert_element((int)the_clause);}
}

void bool_ls_solver::sat_a_clause(uint64_t the_clause){
    uint64_t index,last_item;
    //use the position of the clause to store the last unsat clause in stack
    if(_clauses[the_clause].is_hard==true&&_index_in_unsat_hard_clauses[the_clause]!=-1){
        last_item = _unsat_hard_clauses.back();
        _unsat_hard_clauses.pop_back();
        index = _index_in_unsat_hard_clauses[the_clause];
        _index_in_unsat_hard_clauses[the_clause]=-1;
        if(last_item!=the_clause){
            _unsat_hard_clauses[index] = last_item;
            _index_in_unsat_hard_clauses[last_item] = index;
            }
        }
    else if(_clauses[the_clause].is_hard==false&&_index_in_unsat_soft_clauses[the_clause]!=-1){
        last_item = _unsat_soft_clauses.back();
        _unsat_soft_clauses.pop_back();
        index = _index_in_unsat_soft_clauses[the_clause];
        _index_in_unsat_soft_clauses[last_item]=-1;
        if(last_item!=the_clause){
            _unsat_soft_clauses[index] = last_item;
            _index_in_unsat_soft_clauses[last_item] = index;
            }
        }
    pure_bool_unsat_clauses->delete_element((int)the_clause);//将该子句从纯bool假子句中删除
    contain_bool_unsat_clauses->delete_element((int)the_clause);//将该子句从包含bool假子句中删除
    contain_idl_unsat_clauses->delete_element((int)the_clause);//将该子句从包含idl假子句中删除
}

/**********calculate the delta of a lit***********/
int bool_ls_solver::lit_delta(lit& l){
    if(l.is_idl_lit)
    return _solution[l.prevar_idx]-_solution[l.posvar_idx]-l.key;
    else{
        if((_solution[l.prevar_idx]>0&&l.key>0)||(_solution[l.prevar_idx]<0&&l.key<0))return 0;
        else return 1;// 1 or average_k
    }
}
/**************invert a lit****************/
void bool_ls_solver::invert_lit(lit &l){
    if (l.is_idl_lit){
        uint64_t tmp_idx=l.prevar_idx;
        l.prevar_idx=l.posvar_idx;
        l.posvar_idx=tmp_idx;
        l.key=-1-l.key;
    }
    else{l.key*=-1;}
    l.lits_index=-l.lits_index;
}

/**********modify the CClist***********/
void bool_ls_solver::modifyCC(uint64_t var_idx, uint64_t direction){
    uint64_t opposite_direction=(direction+1)%2;
    variable * vp = &(_vars[var_idx]);
    if(vp->is_idl){CClist[2*var_idx+opposite_direction]=0;}
    else{CClist[2*var_idx]=0;}
    for(uint64_t v:vp->neighbor_var_idxs_bool){CClist[2*v]++;}// allow the bool clause neighbor
    if(!vp->is_idl){for(uint64_t v:vp->neighbor_var_idxs_idl){CClist[2*v]++;CClist[2*v+1]++;}}//the bool var, allow the idl clause neighbor
    else{
        if(CCmode==0){for(uint64_t v:_vars[var_idx].neighbor_var_idxs_idl){CClist[2*v]++;CClist[2*v+1]++;}}
        //the idl var with CCmode 0, allow the idl clause neighbor
        else if(CCmode==1){for(uint64_t v:_vars[var_idx].neighbor_var_idxs_in_lit){CClist[2*v]++;CClist[2*v+1]++;}}
        //the idl var with CCmode 1, allow the idl lit neighbor
        else if(CCmode==2){for(uint64_t v:_vars[var_idx].neighbor_var_idxs_in_lit){CClist[2*v+opposite_direction]++;}}
        //the idl var with CCmode 2 allow the opposite direction of idl lit neighbor
    }
}

/**********calculate score and subscore of critical operation***********/
void bool_ls_solver::critical_score_subscore(uint64_t var_idx,int change_value){
    int delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    //number of make_lits in a clause
    int make_break_in_clause=0;
    lit watch_lit;
    //the future min delta containing var
    int new_future_min_delta=INT32_MAX;
    if(var->is_idl){
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        delta_old=lit_delta(l);
        if(var_idx==l.prevar_idx) delta_new=delta_old+change_value;
        else    delta_new=delta_old-change_value;
        if(delta_old<=0&&delta_new>0) make_break_in_clause--;
        else if(delta_old>0&&delta_new<=0) make_break_in_clause++;
        if(delta_new<new_future_min_delta){
            new_future_min_delta=delta_new;
            watch_lit=l;
        }
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l.clause_idx!=var->literals[i+1].clause_idx)||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {
                cp->last_true_lit=cp->watch_lit;
                unsat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num+=cp->literals.size();
                _bool_lit_in_unsat_clause_num+=cp->bool_literals.size();
            }
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {
                sat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num-=cp->literals.size();
                _bool_lit_in_unsat_clause_num-=cp->bool_literals.size();
            }
            lit origin_watch_lit=cp->watch_lit;
            uint64_t origin_sat_count=cp->sat_count;
            cp->sat_count+=make_break_in_clause;
            if(cp->sat_count==1){sat_num_one_clauses->insert_element((int)l.clause_idx);}
            else{sat_num_one_clauses->delete_element((int)l.clause_idx);}
            new_future_min_delta=std::max(0,new_future_min_delta);
            //if new_future_min_delta<=cp->min_delta, then min_delta and watch needs updating if var is changed
            if(new_future_min_delta<=cp->min_delta){
                cp->min_delta=new_future_min_delta;
                cp->watch_lit=watch_lit;
            }
            else if(cp->watch_lit.prevar_idx==var_idx||cp->watch_lit.posvar_idx==var_idx){
                    for(lit lc:cp->literals){
                        if(lc.prevar_idx!=var_idx&&lc.posvar_idx!=var_idx&&(std::max(0,lit_delta(lc))<new_future_min_delta)){
                            new_future_min_delta=std::max(0,lit_delta(lc));
                            watch_lit=lc;
                        }
                    }
                    cp->min_delta=new_future_min_delta;
                    cp->watch_lit=watch_lit;
                }//if new_future_min_delta>cp->min_delta and var_idx belongs to the watch_lit
            if(_num_bool_vars>0){
            if(make_break_in_clause>0){
                if(origin_sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score-=cp->weight;}}
                else if(origin_sat_count==1&&!origin_watch_lit.is_idl_lit){_vars[origin_watch_lit.prevar_idx].score+=cp->weight;}
            }
            if(make_break_in_clause<0){
                if(cp->sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score+=cp->weight;}}
                else if(cp->sat_count==1&&!cp->watch_lit.is_idl_lit){_vars[cp->watch_lit.prevar_idx].score-=cp->weight;}
            }
            }
            new_future_min_delta=INT32_MAX;
            make_break_in_clause=0;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(lit_delta(l)==0){//true to false
                make_break_in_clause=-1;
                new_future_min_delta=1;//TODO::average_k
            }
            else{//false to true
                make_break_in_clause=1;
                new_future_min_delta=0;
            }
            watch_lit=l;
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {
                cp->last_true_lit=cp->watch_lit;
                unsat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num+=cp->literals.size();
                _bool_lit_in_unsat_clause_num+=cp->bool_literals.size();
            }
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {
                sat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num-=cp->literals.size();
                _bool_lit_in_unsat_clause_num-=cp->bool_literals.size();
            }
            lit origin_watch_lit=cp->watch_lit;
            uint64_t origin_sat_count=cp->sat_count;
            cp->sat_count+=make_break_in_clause;
            if(cp->sat_count==1){sat_num_one_clauses->insert_element((int)l.clause_idx);}
            else{sat_num_one_clauses->delete_element((int)l.clause_idx);}
            if(new_future_min_delta<=cp->min_delta){
                cp->min_delta=new_future_min_delta;
                cp->watch_lit=watch_lit;
            }
            else if(cp->watch_lit.prevar_idx==var_idx){
                    for(lit lc:cp->literals){
                        if(lc.prevar_idx!=var_idx&&(std::max(0,lit_delta(lc))<new_future_min_delta)){
                            new_future_min_delta=std::max(0,lit_delta(lc));
                            watch_lit=lc;
                        }
                    }
                    cp->min_delta=new_future_min_delta;
                    cp->watch_lit=watch_lit;
                }
            if(_num_bool_vars>0){
            if(make_break_in_clause>0){
                if(origin_sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score-=cp->weight;}}
                else if(origin_sat_count==1&&!origin_watch_lit.is_idl_lit){_vars[origin_watch_lit.prevar_idx].score+=cp->weight;}
            }
            else if(make_break_in_clause<0){
                if(cp->sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score+=cp->weight;}}
                else if(cp->sat_count==1&&!cp->watch_lit.is_idl_lit){_vars[cp->watch_lit.prevar_idx].score-=cp->weight;}
            }
            }
        }
    }
}
int bool_ls_solver::critical_score(uint64_t var_idx, int change_value,int &safety){
    int critical_score=0;
    safety=0;
    int delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    //number of make_lits in a clause
    int make_break_in_clause=0;
    if(var->is_idl){
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        delta_old=lit_delta(l);
        if(var_idx==l.prevar_idx) delta_new=delta_old+change_value;
        else    delta_new=delta_old-change_value;
        if(delta_old<=0&&delta_new>0) make_break_in_clause--;
        else if(delta_old>0&&delta_new<=0) make_break_in_clause++;
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l.clause_idx!=var->literals[i+1].clause_idx)||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) critical_score+=cp->weight;
            else if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) critical_score-=cp->weight;
            if(cp->sat_count<=1&&cp->sat_count+make_break_in_clause>1){safety++;}
            else if(cp->sat_count>1&&cp->sat_count+make_break_in_clause<=1){safety--;}
            make_break_in_clause=0;
        }
    }
    }
    //if the var is a bool_var, then flip it
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(lit_delta(l)>0){make_break_in_clause=1;}//false to true
            else{make_break_in_clause=-1;}//true to false
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) critical_score+=cp->weight;
            else if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) critical_score-=cp->weight;
            if(cp->sat_count<=1&&cp->sat_count+make_break_in_clause>1){safety++;}
            else if(cp->sat_count>1&&cp->sat_count+make_break_in_clause<=1){safety--;}
        }
    }
    return critical_score;
}

int bool_ls_solver::critical_subscore(uint64_t var_idx,int change_value){
    int critical_subscore=0;
    int delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    //the future min delta containing var
    int new_future_min_delta=INT32_MAX;
    if(var->is_idl){
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        delta_old=lit_delta(l);
        if(var_idx==l.prevar_idx) delta_new=delta_old+change_value;
        else    delta_new=delta_old-change_value;
        if(delta_new<new_future_min_delta){new_future_min_delta=delta_new;}
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l.clause_idx!=var->literals[i+1].clause_idx)||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l.clause_idx]);
            new_future_min_delta=std::max(0,new_future_min_delta);
            if(new_future_min_delta<=cp->min_delta){
                critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
            }
            else{
                //if new_future_min_delta>cp->min_delta and var_idx belongs to the watch_lit
                if(cp->watch_lit.prevar_idx==var_idx||cp->watch_lit.posvar_idx==var_idx){
                    for(lit lc:cp->literals){
                        if(lc.prevar_idx!=var_idx&&lc.posvar_idx!=var_idx&&(std::max(0,lit_delta(lc))<new_future_min_delta)){
                            new_future_min_delta=std::max(0,lit_delta(lc));
                        }
                    }
                    critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
                }
            }
            new_future_min_delta=INT32_MAX;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(lit_delta(l)==0){new_future_min_delta=1;}//TODO::average_k
            else{new_future_min_delta=0;}
            clause *cp=&(_clauses[l.clause_idx]);
            if(new_future_min_delta<=cp->min_delta){critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;}
            else if(cp->watch_lit.prevar_idx==var_idx){
                for(lit lc :cp->literals){
                    if(lc.prevar_idx!=var_idx&&(std::max(0,lit_delta(lc))<new_future_min_delta)){new_future_min_delta=std::max(0,lit_delta(lc));}
                }
                critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
            }
        }
    }
    return critical_subscore;
}

/**********make move***********/

void bool_ls_solver::critical_move(uint64_t var_idx,uint64_t direction){
    if(_vars[var_idx].is_idl){
        int change_value=(direction==0)?(_forward_critical_value[var_idx]):(-_backward_critical_value[var_idx]);
        critical_score_subscore(var_idx, change_value);
        _solution[var_idx]+=change_value;
    }
    else{
//        if(_step>100000){std::cout<<"enter bool opt: "<<_step<<" current unsat clause: "<<_unsat_hard_clauses.size();}
        int origin_score=_vars[var_idx].score;
        critical_score_subscore(var_idx, 0);
        _solution[var_idx]*=-1;
        _vars[var_idx].score=-origin_score;
//        if(_step>100000){std::cout<<"\n after unsat clause: "<<_unsat_hard_clauses.size()<<"  flip var: "<<var_idx<<"\n\n";}
    }
    //step
    if(_vars[var_idx].is_idl){
        last_move[2*var_idx+direction]=_step;
        tabulist[var_idx*2+(direction+1)%2]=_step+3+mt()%10;
        if(CCmode!=-1){modifyCC(var_idx,direction);}
    }
    else{
        last_move[2*var_idx]=_outer_layer_step;
        tabulist[var_idx*2]=_outer_layer_step+3+mt()%10;
        if(CCmode!=-1){modifyCC(var_idx, direction);}
        bool_tabu_tenue=_step+100+mt()%5;
        _outer_layer_step++;//每次外层搜索都要flip一个布尔变量，外层步数加一
    }
}

void bool_ls_solver::swap_from_small_weight_clause(){
    uint64_t min_weight=UINT64_MAX;
    uint64_t min_weight_clause_idx=0;
    for(int i=0;i<45;i++){
        int clause_idx=sat_num_one_clauses->rand_element();
        if(_clauses[clause_idx].weight<min_weight){
            min_weight=_clauses[clause_idx].weight;
            min_weight_clause_idx=clause_idx;
        }
    }
    clause *cl=&(_clauses[min_weight_clause_idx]);
    for(lit l:cl->literals){
        if(l.prevar_idx!=cl->watch_lit.prevar_idx||l.posvar_idx!=cl->watch_lit.posvar_idx||l.key!=cl->watch_lit.key){
            int delta=lit_delta(l);
            int safety;
            if(l.is_idl_lit){
            if(critical_score(l.prevar_idx, -delta, safety)>critical_score(l.posvar_idx, delta, safety)){
                _backward_critical_value[l.prevar_idx]=delta;
                critical_move(l.prevar_idx, 1);
            }
            else{
                _forward_critical_value[l.posvar_idx]=delta;
                critical_move(l.posvar_idx, 0);
            }
            }
            else{critical_move(l.prevar_idx, 0);}
            break;
        }
    }
}

/**********pick move***********/
//pick the  smallest critical move by BMS
int64_t bool_ls_solver::pick_critical_move(int64_t &direction){
    int best_score,score,best_var_idx,cnt,operation;
    int best_value=0;
    int best_safety=INT32_MIN;
    bool BMS=false;
    best_score=1;
    best_var_idx=-1;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
    //determine the critical value
    for(int i=0;i<contain_idl_unsat_clauses->size();i++){
        clause *cl=&(_clauses[contain_idl_unsat_clauses->element_at(i)]);
        for(lit l:cl->idl_literals){
            int delta=lit_delta(l);
           if(_step>tabulist[2*l.posvar_idx]&&CClist[2*l.posvar_idx]>0&&l.posvar_idx!=idl_var_idx_with_most_lits){
//           if((_step>tabulist[2*l.posvar_idx]&&CCmode==-1)||(CClist[2*l.posvar_idx]>0&&CCmode>=0)){
               operation_vec[operation_idx++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
           }
            if(_step>tabulist[2*l.prevar_idx+1]&&CClist[2*l.prevar_idx+1]>0&&l.prevar_idx!=idl_var_idx_with_most_lits){
//           if((_step>tabulist[2*l.prevar_idx+1]&&CCmode==-1)||(CClist[2*l.prevar_idx+1]>0&&CCmode>=0)){
               operation_vec[operation_idx++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
           }
        }
    }
    //go through the forward and backward move of vars, evaluate their score, pick the untabued best one
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            int tmp=operation_vec[operation_idx-i-1];
            operation=operation_vec[idx];
            operation_vec[idx]=tmp;
        }
        else{operation=operation_vec[i];}
//        operation=operation_vec[i];
        int var_idx,operation_direction,critical_value,safety;
        hash_opt(operation, var_idx, operation_direction, critical_value);
            score=critical_score(var_idx, critical_value,safety);
        uint64_t last_move_step=last_move[2*var_idx+(operation_direction+1)%2];
        if(score>best_score||(score==best_score&&safety>best_safety)||(score==best_score&&safety==best_safety&&last_move_step<best_last_move)){
                best_safety=safety;
                best_score=score;
                best_var_idx=var_idx;
                direction=operation_direction;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    //if there is untabu decreasing move
    if(best_var_idx!=-1){
        if(best_value>0){_forward_critical_value[best_var_idx]=best_value;}
        else{_backward_critical_value[best_var_idx]=-best_value;}
        return best_var_idx;}
    //TODO:aspiration
    //choose from swap operations if there is no decreasing unsat critical
    operation_idx=0;
  for(int i=0;operation_idx<45&&i<100;i++){add_swap_operation(operation_idx);}
//    while (operation_idx<45) {add_swap_operation(operation_idx);}
    for(int i=0;i<operation_idx;i++){
        operation=operation_vec[i];
        int var_idx,operation_direction,critical_value,safety;
        hash_opt(operation, var_idx, operation_direction, critical_value);
            score=critical_score(var_idx, critical_value,safety);
//            if(score>best_score||(score==best_score&&last_move[2*var_idx+(operation_direction+1)%2]<best_last_move)){
        uint64_t last_move_step=(_vars[var_idx].is_idl)?last_move[2*var_idx+(operation_direction+1)%2]:last_move[2*var_idx];
        if(score>best_score||(score==best_score&&safety>best_safety)||(score==best_score&&safety==best_safety&&last_move_step<best_last_move)){
                best_safety=safety;
                best_score=score;
                best_var_idx=var_idx;
                direction=operation_direction;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    if(best_var_idx!=-1){
        if(best_value>0){_forward_critical_value[best_var_idx]=best_value;}
        else{_backward_critical_value[best_var_idx]=-best_value;}
        return best_var_idx;}
    //update weight
    if(mt()%10000>smooth_probability){update_clause_weight_critical();}
    else {smooth_clause_weight_critical();}
    random_walk_all();
    return best_var_idx;
}
//从所有假子句中选择一个未禁的分数最高的布尔变量，如果不存在就随机布尔步
//当进入外层搜索时，要首先flip“第一个”布尔变量（前提是存在带bool变量的假子句），这是为了让内层骨架与之前有所不同，遍历所有带bool变量的假子句（如果首次进入，这些子句应该全是混合子句，因为首次进入时没有纯布尔假子句），该布尔变量应该是希望能
//尽量多地满足子句，任何子句（混合子句）,选择最大分数的（不需要大于0，因为外层搜索属于疏散操作），如果不存在（所有操作都被禁忌了），则进入随机步
//随机步时：随机选一个假（带bool变量的）子句，从中选一个最老的布尔变量flip
int64_t bool_ls_solver::pick_move_bool_first(){
    int best_score,score,best_var_idx,cnt,operation;
    int best_value=INT32_MIN;
    bool BMS=false;
    best_score=1;
    best_var_idx=-1;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
    for(int i=0;i<contain_bool_unsat_clauses->size();i++){
        clause *cl=&(_clauses[contain_bool_unsat_clauses->element_at(i)]);
        for(lit l:cl->bool_literals){
            if(is_chosen_bool_var[l.prevar_idx])continue;
            if(_outer_layer_step>tabulist[2*l.prevar_idx]&&CClist[2*l.prevar_idx]>0) {
                operation_vec[operation_idx++]=(int)l.prevar_idx;
                is_chosen_bool_var[l.prevar_idx]=true;
            }
        }
    }
    for(int i=0;i<operation_idx;i++){is_chosen_bool_var[operation_vec[i]]=false;}// recover chosen_bool_var
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            int tmp=operation_vec[operation_idx-i-1];
            operation=operation_vec[idx];
            operation_vec[idx]=tmp;
        }
        else{operation=operation_vec[i];}
        int var_idx,operation_direction,critical_value;
        hash_opt(operation, var_idx, operation_direction, critical_value);
        score=_vars[var_idx].score;
        uint64_t last_move_step=last_move[2*var_idx];
        if(score>best_score||(score==best_score&&last_move_step<best_last_move)){
                best_score=score;
                best_var_idx=var_idx;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    //if there is untabu move
    if(best_var_idx!=-1){return best_var_idx;}
    //else return the oldest one in a random clause containing bool vars
    best_last_move=UINT64_MAX;
    int random_idx=mt()%contain_bool_unsat_clauses->size();
    clause *cl=&(_clauses[contain_bool_unsat_clauses->element_at(random_idx)]);
    for(lit l:cl->bool_literals){
        uint64_t last_move_step=last_move[2*l.prevar_idx];
        if(last_move_step<best_last_move){
            best_last_move=last_move_step;
            best_var_idx=(int)l.prevar_idx;
        }
    }
    return best_var_idx;
}
//计算翻转该变量可以让pure bool clauses的权重变化量
int bool_ls_solver::outer_layer_score(uint64_t var_idx){
    int outer_score=0;
    for(lit &l:_vars[var_idx].literals){
        clause *cl=&(_clauses[l.clause_idx]);
        if(cl->is_pure_boolean){
            if(cl->sat_count==0){outer_score+=cl->weight;}
            else if(cl->sat_count==1&&cl->watch_lit.prevar_idx==var_idx){outer_score-=cl->weight;}
        }
    }
    return outer_score;
}
//当flip完第一个bool变量之后，导致出现了未满足的纯布尔子句，为了使其满足，就要继续flip布尔变量，此时希望可以
//首先尽量多地满足纯布尔子句（外层分数），其次原score可以作为副分数，遍历所有纯布尔假子句，找到外层分数最大且大于0的未禁忌变量，如果不存在，就先对纯布尔假子句加权然后进入外层随机步
//随机步时：随机选一个纯布尔假子句中，从中选择一个最老布尔变量flip
int64_t bool_ls_solver::pick_move_bool_outer_layer(){
    int best_score,score,best_outer_score,outer_score,best_var_idx,cnt,operation;
    int best_value=0;
    bool BMS=false;
    best_score=INT32_MIN;
    best_outer_score=1;
    best_var_idx=-1;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
    for(int i=0;i<pure_bool_unsat_clauses->size();i++){
        clause *cl=&(_clauses[pure_bool_unsat_clauses->element_at(i)]);
        for(lit l:cl->bool_literals){
            if(is_chosen_bool_var[l.prevar_idx])continue;
            if(_outer_layer_step>tabulist[2*l.prevar_idx]&&CClist[2*l.prevar_idx]>0) {
                operation_vec[operation_idx++]=(int)l.prevar_idx;
                is_chosen_bool_var[l.prevar_idx]=true;
            }
        }
    }
    for(int i=0;i<operation_idx;i++){is_chosen_bool_var[operation_vec[i]]=false;}// recover chosen_bool_var
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            int tmp=operation_vec[operation_idx-i-1];
            operation=operation_vec[idx];
            operation_vec[idx]=tmp;
        }
        else{operation=operation_vec[i];}
        int var_idx,operation_direction,critical_value;
        hash_opt(operation, var_idx, operation_direction, critical_value);
        outer_score=outer_layer_score(var_idx);
        score=_vars[var_idx].score;
        uint64_t last_move_step=last_move[2*var_idx];
        if(outer_score>best_outer_score||(outer_score==best_outer_score&&score>best_score)||(outer_score==best_outer_score&&score==best_score&&last_move_step<best_last_move)){
                best_outer_score=outer_score;
                best_score=score;
                best_var_idx=var_idx;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    //if there is untabu decreasing move
    if(best_var_idx!=-1){return best_var_idx;}
    //update weight of pure bool unsat clauses, and random walk by picking the oldest var in a random pure bool clause
    for(int i=0;i<pure_bool_unsat_clauses->size();i++){
        clause *cl=&(_clauses[pure_bool_unsat_clauses->element_at(i)]);
        cl->weight+=h_inc;
        for(lit &l:cl->bool_literals){_vars[l.prevar_idx].score+=h_inc;}
    }
    total_clause_weight+=h_inc*pure_bool_unsat_clauses->size();
    best_last_move=UINT64_MAX;
    int random_idx=mt()%pure_bool_unsat_clauses->size();
    clause *cl=&(_clauses[pure_bool_unsat_clauses->element_at(random_idx)]);
    for(lit l:cl->bool_literals){
        uint64_t last_move_step=last_move[2*l.prevar_idx];
        if(last_move_step<best_last_move){
            best_last_move=last_move_step;
            best_var_idx=(int)l.prevar_idx;
        }
    }
    return best_var_idx;
}

//a bool var with score>0 is from a falsified clause, no need to select from sat_num_one_clause, so the swap operation is dedicated for idl var
void bool_ls_solver::add_swap_operation(int &operation_idx){
    int c=sat_num_one_clauses->element_at(mt()%sat_num_one_clauses->size());
    clause *cl=&(_clauses[c]);
    for(lit l:cl->idl_literals){
        if(l.prevar_idx!=cl->watch_lit.prevar_idx||l.posvar_idx!=cl->watch_lit.posvar_idx||l.key!=cl->watch_lit.key){
            int delta=lit_delta(l);
            if(l.posvar_idx!=idl_var_idx_with_most_lits)
            operation_vec[operation_idx++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
            if(l.prevar_idx!=idl_var_idx_with_most_lits)
            operation_vec[operation_idx++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
        }
    }
}

/**********random walk************/
//only random walk on those integer vars，在此时已经没有纯布尔假子句了，因此遍历3个假子句必然存在idl操作
//随机选3个子句，最多5个整数操作，从中选择副分数最大的
void bool_ls_solver::random_walk_all(){
    uint64_t c;
    uint64_t best_operation_idx_idl;
    //best is the best operation of all, second is the best of non-last-true
    best_operation_idx_idl=0;
    uint64_t        operation_idx_idl=0;
    for(int i=0;i<3&&operation_idx_idl<5;i++){
        int random_idx=mt()%contain_idl_unsat_clauses->size();
        c=contain_idl_unsat_clauses->element_at(random_idx);
        clause *cp=&(_clauses[c]);
        for(lit l:cp->idl_literals){
            int delta=lit_delta(l);
            operation_vec_idl[operation_idx_idl++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
            operation_vec_idl[operation_idx_idl++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
        }
    }
    int subscore,var_idx,operation_direction,critical_value;
    int best_subscore_idl=INT32_MAX;
    uint64_t best_last_move_idl=UINT64_MAX;
    for(uint64_t i=0;i<operation_idx_idl;i++){
        hash_opt(operation_vec_idl[i], var_idx, operation_direction, critical_value);
        subscore=critical_subscore(var_idx, critical_value);
        uint64_t last_move_step=last_move[2*var_idx+(operation_direction+1)%2];
        if(subscore<best_subscore_idl||(subscore==best_subscore_idl&&last_move_step<best_last_move_idl)){
            best_subscore_idl=subscore;
            best_last_move_idl=last_move_step;
            best_operation_idx_idl=i;
        }
    }
        hash_opt(operation_vec_idl[best_operation_idx_idl], var_idx, operation_direction, critical_value);
        if(critical_value>0){_forward_critical_value[var_idx]=critical_value;}
        else{_backward_critical_value[var_idx]=-critical_value;}
    critical_move(var_idx, operation_direction);
}
/**********update solution***********/
bool bool_ls_solver::update_best_solution(){
    bool improve=false;
    if(_unsat_hard_clauses.size()<_best_found_hard_cost_this_restart){
        improve=true;
        _best_found_hard_cost_this_restart=_unsat_hard_clauses.size();
//        cout<<"best_found_hard_cost_this_turn:"<<_best_found_hard_cost_this_restart<<endl;
    }
    if((_unsat_hard_clauses.size()<_best_found_hard_cost)||(_unsat_hard_clauses.size()==0&&_unsat_soft_clauses.size()<_best_found_soft_cost)){
        improve=true;
        _best_cost_time=TimeElapsed();
        _best_found_hard_cost=_unsat_hard_clauses.size();
//        cout<<"best_found_hard_cost"<<_best_found_hard_cost<<endl<<"best_found_soft_cost:"<<_best_found_soft_cost<<" best_step:"<<_step<<" time"<<_best_cost_time<<endl<<endl;
        _best_solution=_solution;
    }
    if(_unsat_hard_clauses.size()==0&&_unsat_soft_clauses.size()<_best_found_soft_cost){
        _best_found_soft_cost=_unsat_soft_clauses.size();
    }
    return improve;
}

bool bool_ls_solver::update_inner_best_solution(){
    if(_unsat_hard_clauses.size()<_best_found_hard_cost_this_inner){
        _best_found_hard_cost_this_inner=_unsat_hard_clauses.size();
        return true;
    }
    return false;
}

double bool_ls_solver::TimeElapsed(){
    std::chrono::steady_clock::time_point finish = std::chrono::steady_clock::now();
    std::chrono::duration<double> duration = finish - start;
    return duration.count();
}

void bool_ls_solver::hash_opt(int operation,int &var_idx,int &operation_direction,int &critical_value){
    if(operation>0){
        var_idx=operation%(int)_num_vars;
        operation_direction=0;
        critical_value=operation/(int)_num_vars;
    }
    else{
        operation_direction=1;
        var_idx=(operation%(int)_num_vars+(int)_num_vars);
        if(var_idx==(int)_num_vars)var_idx=0;
        critical_value=(operation-var_idx)/(int)_num_vars;
    }
}

/**********clause weighting***********/

//only add clause weight
void bool_ls_solver::update_clause_weight_critical(){
    clause *cp;
    for(uint64_t c:_unsat_soft_clauses){
        cp=&(_clauses[c]);
        if(cp->weight>softclause_weight_threshold)
            continue;
        cp->weight++;
    }
    for(uint64_t c:_unsat_hard_clauses){
        cp=&(_clauses[c]);
        cp->weight+=h_inc;
        for(lit &l:cp->bool_literals){_vars[l.prevar_idx].score+=h_inc;}
    }
    total_clause_weight+=_unsat_soft_clauses.size();
    total_clause_weight+=h_inc*_unsat_hard_clauses.size();
}

void bool_ls_solver::smooth_clause_weight(){
    clause *cp;
    uint64_t scale_ave_weight=total_clause_weight/_num_clauses*(1-_swt_p);
    total_clause_weight=0;
    for(uint64_t c=0;c<_num_clauses;c++){
        cp=&(_clauses[c]);
        cp->weight=cp->weight*_swt_p+scale_ave_weight;
        if(cp->weight<1){cp->weight=1;}
        total_clause_weight+=cp->weight;
    }
}
//only minus the weight of clauses, score and subscore are not updated
void bool_ls_solver::smooth_clause_weight_critical(){
    clause *cp;
    int weight_delta;
    for(uint64_t c=0;c<_num_clauses;c++){
       if(_clauses[c].weight>1&&_index_in_unsat_hard_clauses[c]==-1&&_index_in_unsat_soft_clauses[c]==-1){
            cp=&(_clauses[c]);
            weight_delta=(cp->is_hard)?h_inc:1;
            cp->weight-=weight_delta;
            total_clause_weight-=weight_delta;
           if(cp->sat_count==1&&!cp->watch_lit.is_idl_lit){_vars[cp->watch_lit.prevar_idx].score+=weight_delta;}
        }
    }
}
int64_t bool_ls_solver::get_cost(){
    if(_unsat_hard_clauses.size()==0)
        return _unsat_soft_clauses.size();
    else
        return -1;
}
/***************print*****************/
void bool_ls_solver::print_formula(){
    int i=0;
    for(clause & cl :_clauses){
        std::cout<<i++<<"\n";
        for(lit & l: cl.literals){
            print_literal(l);
        }
        std::cout<<"\n";
    }
}

void bool_ls_solver::print_literal(lit &l){
    if(l.is_idl_lit)
    std::cout<<_vars[l.prevar_idx].var_name<<'-'<<_vars[l.posvar_idx].var_name<<"<="<<l.key<<"\n";
    else{
        if(l.key<0)std::cout<<"-";
        std::cout<<_vars[l.prevar_idx].var_name<<"\n";
        }
}

/********checker*********/
bool bool_ls_solver::check_solution(){
    clause *cp;
    uint64_t unsat_hard_num=0;
    uint64_t unsat_soft_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        bool unsat_flag=false;
        uint64_t sat_count=0;
        cp=&(_clauses[i]);
        for(lit l: cp->literals){
            int preval=_solution[l.prevar_idx];
            int posval=_solution[l.posvar_idx];
            if((l.is_idl_lit&&preval-posval<=l.key)||(!l.is_idl_lit&&preval*l.key>0)){
                unsat_flag=true;
                sat_count++;
            }
        }
        if(sat_count!=_clauses[i].sat_count){
            std::cout<<"sat_count wrong!\n";
        }
        if(!unsat_flag){
            if(cp->is_hard) unsat_hard_num++;
            else unsat_soft_num++;
        }
    }
    if(unsat_hard_num==_unsat_hard_clauses.size())
        std::cout<<"right solution\n";
    else
        std::cout<<"wrong solution\n";
    return unsat_hard_num==_unsat_hard_clauses.size();
}

bool bool_ls_solver::check_best_solution(){
    clause *cp;
    uint64_t unsat_hard_num=0;
    uint64_t unsat_soft_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        bool unsat_flag=false;
        uint64_t sat_count=0;
        cp=&(_clauses[i]);
        for(lit l: cp->literals){
            int preval=_best_solution[l.prevar_idx];
            if(l.is_idl_lit){
            int posval=_best_solution[l.posvar_idx];
            if(preval-posval<=l.key){
                unsat_flag=true;
                sat_count++;
            }
            }
            else if((preval>0&&l.key>0)||(preval<0&&l.key<0)){
                unsat_flag=true;
                sat_count++;
            }
        }

        if(!unsat_flag){
            if(cp->is_hard) unsat_hard_num++;
            else unsat_soft_num++;
        }
    }
    if(unsat_hard_num==_best_found_hard_cost)
        std::cout<<"right solution\n";
    else
        std::cout<<"wrong solution\n";
    return unsat_hard_num==_best_found_hard_cost;
}
/************local search****************/
void bool_ls_solver::outer_layer_search(){
    int64_t flipv;
    // first pick a bool var to flip, in order to modify the "skeleton" of integer formula
    //首先翻转一个bool变量，为了让当前整数公式的骨架变得不同，属于疏散操作，注意此时不存在纯布尔子句，该变量会首先从带bool变量的假子句中选择，遍历这些子句，从中找出未被禁忌的分数最大的变量（不用大于0），如果没有就进入随机步，从随机一个带bool的子句中选一个最老的布尔变量
    flipv=pick_move_bool_first();
    if(flipv!=-1){critical_move(flipv,0);}
    //empty the pure bool unsat clauses
    //不断从纯布尔子句中选择（分数>0的）分数最大的未禁忌变量，如果没有就进入随机步，从随机一个纯bool子句中选择一个最老的布尔变量
   while(pure_bool_unsat_clauses->size()!=0){
       flipv=pick_move_bool_outer_layer();
       if(flipv!=-1) {critical_move(flipv,0);}
   }
    _best_found_hard_cost_this_inner=_unsat_hard_clauses.size();
}

bool bool_ls_solver::local_search(){
    int64_t flipv;
    int64_t direction;//0 means moving forward while 1 means moving backward
    uint64_t no_improve_cnt=0;
    uint64_t no_improve_cnt_inner=UINT64_MAX;//确保进来第一次先进入外层搜索
    start = std::chrono::steady_clock::now();
    initialize();
    _outer_layer_step=1;
    for(_step=1;_step<_max_step;_step++){
        if(0==_unsat_hard_clauses.size()){return true;}
        if(_step%1000==0&&(TimeElapsed()>_cutoff)){break;}
        if(no_improve_cnt>500000){initialize();no_improve_cnt=0;}
        if(_unsat_hard_clauses.size()==pure_bool_unsat_clauses->size()||(no_improve_cnt_inner>1000&&contain_bool_unsat_clauses->size()>0)){
        // if(mt()%_lit_in_unsast_clause_num<_bool_lit_in_unsat_clause_num){
            outer_layer_search();
            no_improve_cnt_inner=0;
        }
        //当在禁忌中，或者所有假子句都是纯整数的，则不能进入外层（因为如果假子句中没有布尔，则翻转布尔变量不能使其变真,只会让问题变得更难，相当于加约束）
        else{
            flipv=pick_critical_move(direction);
            if(flipv!=-1) {critical_move(flipv, direction);}
        }
        if(update_best_solution()) no_improve_cnt=0;
        else                        no_improve_cnt++;
        if(update_inner_best_solution()) no_improve_cnt_inner=0;
        else                        no_improve_cnt_inner++;
    }
    return false;
}
};