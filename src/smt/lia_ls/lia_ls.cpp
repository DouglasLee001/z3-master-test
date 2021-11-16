#include "smt/lia_ls/lia_ls.h"
namespace lia{
//input transformation
void ls_solver::split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern=" "){
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

void ls_solver::build_lits(std::string &in_string){
    std::vector<std::string> vec;
    split_string(in_string, vec);
    if(vec[0]=="0"){_lits[0].lits_index=0; return;}//true literal
    int lit_index=std::atoi(vec[0].c_str());
    if(vec[1][1]=='!'){_lits[lit_index].lits_index=0;return;}//lits index==0 means that the lit is true
    lit *l=&(_lits[lit_index]);
    if(vec.size()>2){
        if(vec.size()>6){
            l->lits_index=std::atoi(vec[0].c_str());
            int idx=5;
            for(;idx<vec.size();idx++){
                if(vec[idx]==")"){break;}
                if(vec[idx]=="("){
                    idx+=2;
                    int coff=std::atoi(vec[idx].c_str());
                    if(coff>0){
                        l->pos_coff.push_back(coff);
                        l->pos_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[++idx]));
                    }
                    else{
                        l->neg_coff.push_back(-coff);
                        l->neg_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[++idx]));
                    }
                    idx++;
                }
                else{
                    l->pos_coff.push_back(1);
                    l->pos_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[idx]));
                }
                _num_opt+=l->pos_coff.size();
                _num_opt+=l->neg_coff.size();
            }
            l->key=-std::atoi(vec[++idx].c_str());
            if(vec[2]==">="){l->key++;invert_lit(*l);}
        }//( <= ( + x1 ( * -1 x2 ) x7 ( * -1 x8 ) ) 0 )
        else{
            _bound_lits.push_back(lit_index);
            l->lits_index=0;
            int bound=std::atoi(vec[4].c_str());
            uint64_t var_idx=transfer_name_to_tmp_var(vec[3]);
            if(vec[2]==">="){_tmp_vars[var_idx].low_bound=std::max(_tmp_vars[var_idx].low_bound,bound);}
            else if(vec[2]=="<="){_tmp_vars[var_idx].upper_bound=std::min(_tmp_vars[var_idx].upper_bound,bound);}
        }//( >= x 0 )
        
    }//lia lit
    else{
        
    }//boolean lit
    
}

void ls_solver::build_instance(std::vector<std::vector<int> >& clause_vec){
    reduce_vars();
    _clauses.resize(clause_vec.size());
    _num_clauses=0;
    for (auto clause_curr:clause_vec) {
        bool is_tautology=false;
        for (auto l_idx : clause_curr) {if(_lits[std::abs(l_idx)].lits_index==0){is_tautology=true;break;}}
        if(is_tautology){continue;}
        for (auto l_idx : clause_curr) {
            _clauses[_num_clauses].literals.push_back(l_idx);
            lit *l=&(_lits[l_idx]);
            variable *v;
            for(int i=0;i<l->pos_coff.size();i++){
                v=&(_vars[l->pos_coff_var_idx[i]]);
                v->literals.push_back(l_idx);
                v->literal_clause.push_back((int)_num_clauses);
                v->literal_coff.push_back(l->pos_coff[i]);
            }
            for(int i=0;i<l->neg_coff.size();i++){
                v=&(_vars[l->neg_coff_var_idx[i]]);
                v->literals.push_back(l_idx);
                v->literal_clause.push_back((int)_num_clauses);
                v->literal_coff.push_back(-l->neg_coff[i]);
            }
        }
        _num_clauses++;
    }
    for(variable & v:_vars){
        int pre_clause_idx=INT32_MAX;
        for(int i=0;i<v.literal_clause.size();i++){
            int tmp_clause_idx=v.literal_clause[i];
            if(pre_clause_idx!=tmp_clause_idx){
                v.clause_idxs.push_back(tmp_clause_idx);
                pre_clause_idx=tmp_clause_idx;
            }
        }
    }
    _num_vars=_vars.size();
    best_found_cost=(int)_num_clauses;
    make_space();
}

uint64_t ls_solver::transfer_name_to_var(std::string & name){
    if(name2var.find(name)==name2var.end()){
        name2var[name]=_vars.size();
        variable var;
        var.clause_idxs.reserve(64);
        var.literals.reserve(64);
        var.literal_clause.reserve(64);
        var.literal_coff.reserve(64);
        var.var_name=name;
        _vars.push_back(var);
        return _vars.size()-1;
    }
    else return name2var[name];
}

uint64_t ls_solver::transfer_name_to_tmp_var(std::string & name){
    if(name2var.find(name)==name2var.end()){
        name2var[name]=_tmp_vars.size();
        variable var;
        var.var_name=name;
        _tmp_vars.push_back(var);
        return _tmp_vars.size()-1;
    }
    else return name2var[name];
}

void ls_solver::reduce_vars(){
    const uint64_t tmp_vars_size=_tmp_vars.size();
    std::vector<int> hash_map(tmp_vars_size*tmp_vars_size,0);//hash_map[A*(size)+b]=n means A-B has occurred n times
    std::vector<int> occur_time(tmp_vars_size,0);//occur_time[a]=n means that a has occured in lits for n times
    Array *pair_x=new Array((int)tmp_vars_size);
    Array *pair_y=new Array((int)tmp_vars_size);
    lit *l;
    variable * original_var;
    variable * new_var;
    std::string var_name;
    int pos_var_idx,neg_var_idx,original_var_idx;
    //calculate the hash_map
    for(uint64_t l_idx=0;l_idx<_num_lits;l_idx++){
        l=&(_lits[l_idx]);
        if(l->lits_index==0){continue;}
        for(int i=0;i<l->pos_coff.size();i++){
            pos_var_idx=l->pos_coff_var_idx[i];
            for(int j=0;j<l->neg_coff.size();j++){
                if(l->pos_coff[i]!=l->neg_coff[j]){continue;}
                neg_var_idx=l->neg_coff_var_idx[j];
                if(neg_var_idx<pos_var_idx){hash_map[neg_var_idx*tmp_vars_size+pos_var_idx]++;}//small_idx* num_var+ large_idx
                else{hash_map[pos_var_idx*tmp_vars_size+neg_var_idx]++;}
            }
        }
    }
    //calculate the occur time
    for(uint64_t l_idx=0;l_idx<_num_lits;l_idx++){
        l=&(_lits[l_idx]);
        if(l->lits_index==0){continue;}
        for(int i=0;i<l->pos_coff.size();i++){occur_time[l->pos_coff_var_idx[i]]++;}
        for(int i=0;i<l->neg_coff.size();i++){occur_time[l->neg_coff_var_idx[i]]++;}
    }
    //calculate the x-y pair
    for(int pre_idx=0;pre_idx<tmp_vars_size;pre_idx++){
        if(pair_y->is_in_array(pre_idx)){continue;}//prevent reinsert
        for(int pos_idx=pre_idx;pos_idx<tmp_vars_size;pos_idx++){
            if(hash_map[pre_idx*tmp_vars_size+pos_idx]==occur_time[pre_idx]){
                pair_x->insert_element(pre_idx);
                pair_y->insert_element(pos_idx);
                break;
            }
        }
    }
    name2var.clear();
    //rewrite lits
    for(uint64_t l_idx=0;l_idx<_num_lits;l_idx++){
        l=&(_lits[l_idx]);
        lit new_lit;
        if(l->lits_index==0){continue;}
        new_lit.key=l->key;
        new_lit.lits_index=l->lits_index;
        for(int i=0;i<l->pos_coff.size();i++){
            original_var_idx=l->pos_coff_var_idx[i];
            original_var=&(_tmp_vars[original_var_idx]);
            if(pair_x->is_in_array(original_var_idx)){
                new_lit.pos_coff.push_back(l->pos_coff[i]);
//                var_name="_new_var_"+std::to_string(pair_x->index_of(original_var_idx));
                var_name="_new_var_"+original_var->var_name;
                new_lit.pos_coff_var_idx.push_back((int)transfer_name_to_var(var_name));
            }
            else if(pair_y->is_in_array(original_var_idx)){
                new_lit.neg_coff.push_back(l->pos_coff[i]);
//                var_name="_new_var_"+std::to_string(pair_y->index_of(original_var_idx));
                var_name="_new_var_"+_tmp_vars[pair_x->element_at(pair_y->index_of(original_var_idx))].var_name;
                new_lit.neg_coff_var_idx.push_back((int)transfer_name_to_var(var_name));
            }
            else{
                new_lit.pos_coff.push_back(l->pos_coff[i]);
                new_lit.pos_coff_var_idx.push_back((int)transfer_name_to_var(original_var->var_name));
            }
        }
        for(int i=0;i<l->neg_coff.size();i++){
            original_var_idx=l->neg_coff_var_idx[i];
            original_var=&(_tmp_vars[original_var_idx]);
            if(!pair_x->is_in_array(original_var_idx)&&!pair_y->is_in_array(original_var_idx)){
                new_lit.neg_coff.push_back(l->neg_coff[i]);
                new_lit.neg_coff_var_idx.push_back((int)transfer_name_to_var(original_var->var_name));
            }
        }
        _lits[l_idx]=new_lit;
    }
    //set low and upbound
    for(original_var_idx=0;original_var_idx<_tmp_vars.size();original_var_idx++){
        original_var=&(_tmp_vars[original_var_idx]);
        //original var
        if(!pair_x->is_in_array(original_var_idx)&&!pair_y->is_in_array(original_var_idx)){
            new_var=&(_vars[transfer_name_to_var(original_var->var_name)]);
            new_var->low_bound=original_var->low_bound;
            new_var->upper_bound=original_var->upper_bound;
        }
        //new var
        else if(pair_x->is_in_array(original_var_idx)){
            int pair_idx=pair_x->index_of(original_var_idx);
//            var_name="_new_var_"+std::to_string(pair_idx);
            var_name="_new_var_"+original_var->var_name;
            new_var=&(_vars[transfer_name_to_var(var_name)]);
            new_var->upper_bound=original_var->upper_bound-_tmp_vars[pair_y->element_at(pair_idx)].low_bound;
            new_var->low_bound=original_var->low_bound-_tmp_vars[pair_y->element_at(pair_idx)].upper_bound;
        }
    }
    int num_var_with_bound=0;
    for(int var_idx=0;var_idx<_vars.size();var_idx++){
        new_var=&(_vars[var_idx]);
        if(new_var->low_bound!=-max_int){
            int lit_idx=_bound_lits[num_var_with_bound++];
            l=&(_lits[lit_idx]);
            l->lits_index=lit_idx;
            l->neg_coff.push_back(1);
            l->neg_coff_var_idx.push_back(var_idx);
            l->key=new_var->low_bound;
            new_var->low_bound=-max_int;
        }
        if(new_var->upper_bound!=max_int){
            int lit_idx=_bound_lits[num_var_with_bound++];
            l=&(_lits[lit_idx]);
            l->lits_index=lit_idx;
            l->pos_coff.push_back(1);
            l->pos_coff_var_idx.push_back(var_idx);
            l->key=-new_var->upper_bound;
            new_var->upper_bound=max_int;
        }
    }
}

//initialize
ls_solver::ls_solver()
:_swt_p(0.3),
_swt_threshold(50),
smooth_probability(3),
_cutoff(1200),
_additional_len(10),
_max_step(UINT64_MAX),
CC_mode(-1)
{mt.seed(1);}

ls_solver::ls_solver(int random_seed)
:_swt_p(0.3),
_swt_threshold(50),
smooth_probability(3),
_cutoff(1200),
_additional_len(10),
_max_step(UINT64_MAX),
CC_mode(-1)
{mt.seed(random_seed);}


void ls_solver::make_space(){
    _solution.resize(_num_vars+_additional_len);
    _best_solutin.resize(_num_vars+_additional_len);
    tabulist.resize(2*_num_vars+_additional_len,0);
    CClist.resize(2*_num_vars+_additional_len,1);
    operation_var_idx_vec.resize(_num_opt+_additional_len);
    operation_change_value_vec.resize(_num_opt+_additional_len);
    last_move.resize(2*_num_vars+_additional_len,0);
    unsat_clauses=new Array((int)_num_clauses+(int)_additional_len);
}

void ls_solver::initialize(){
    clear_prev_data();
    construct_slution_score();
    initialize_lit_datas();
    initialize_clause_datas();
    initialize_variable_datas();
    best_found_this_restart=unsat_clauses->size();
    update_best_solution();
}

void ls_solver::initialize_variable_datas(){
    
}
//initialize the delta of each literal by delta_lit operation
void ls_solver::initialize_lit_datas(){
    for(int i=0;i<_num_lits;i++){
        if(_lits[i].lits_index!=0){_lits[i].delta=delta_lit(_lits[i]);}
    }
}
//set the sat num of each clause, and sat/unsat a clause
void ls_solver::initialize_clause_datas(){
    for(uint64_t c=0;c<_num_clauses;c++){
        clause *cl=&(_clauses[c]);
        cl->sat_count=0;
        cl->weight=1;
        for(int l_idx:cl->literals){
            if((l_idx>0&&_lits[l_idx].delta<=0)||(l_idx<0&&_lits[l_idx].delta>0)){cl->sat_count++;}
        }
        if(cl->sat_count==0){unsat_a_clause(c);}
        else{sat_a_clause(c);}
    }
    total_clause_weight=_num_clauses;
}

void ls_solver::build_neighbor(){
    
}

//random walk
void ls_solver::update_clause_weight(){
    for(int i=0;i<unsat_clauses->size();i++){
        _clauses[unsat_clauses->element_at(i)].weight++;
    }
    total_clause_weight+=unsat_clauses->size();
}

void ls_solver::smooth_clause_weight(){
    for(int i=0;i<_num_clauses;i++){
        if(_clauses[i].weight>1&&!unsat_clauses->is_in_array(i)){
            _clauses[i].weight--;
            total_clause_weight--;
        }
    }
}

void ls_solver::random_walk(){
    int clause_idx,operation_idx,change_value,var_idx,score,operation_direction;
    int best_score=INT32_MIN;
    int best_operation_idx=0;
    uint64_t best_last_move=UINT64_MAX;
    uint64_t last_move_step;
    operation_idx=0;
    clause *cp;
    lit *l;
    //determine the operations
    for(int i=0;i<3&&operation_idx<5;i++){
        clause_idx=unsat_clauses->element_at(mt()%unsat_clauses->size());
        cp=&(_clauses[clause_idx]);
        for(int l_idx:cp->literals){
            l=&(_lits[std::abs(l_idx)]);
            for(int k=0;k<l->pos_coff.size();k++){
                var_idx=l->pos_coff_var_idx[k];
                change_value=(l_idx>0)?devide(-l->delta,l->pos_coff[i]):devide(1-l->delta, l->pos_coff[i]);
                insert_operation(var_idx, change_value, operation_idx);
            }
            for(int k=0;k<l->neg_coff.size();k++){
                var_idx=l->neg_coff_var_idx[k];
                change_value=(l_idx>0)?devide(l->delta, l->neg_coff[i]):devide(l->delta-1, l->neg_coff[i]);
                insert_operation(var_idx, change_value, operation_idx);
            }
        }
    }
    //choose the best operation
    for(int i=0;i<operation_idx;i++){
        var_idx=operation_var_idx_vec[i];
        change_value=operation_change_value_vec[i];
        score=critical_score(var_idx, change_value);
        operation_direction=(change_value>0)?0:1;
        last_move_step=last_move[2*var_idx+(operation_direction+1)%2];
        if(score>best_score||(score==best_score&&last_move_step<best_last_move)){
            best_score=score;
            best_last_move=last_move_step;
            best_operation_idx=i;
        }
    }
    //make move
    var_idx=operation_var_idx_vec[best_operation_idx];
    change_value=operation_change_value_vec[best_operation_idx];
    critical_move(var_idx, change_value);
}

//construction
void ls_solver::construct_slution_score(){
//TODO::this is a temp function, setting all vars 0
    for(int i=0;i<_num_vars;i++){
        if(_vars[i].low_bound>0){_solution[i]=_vars[i].low_bound;}
        else if(_vars[i].upper_bound<0){_solution[i]=_vars[i].upper_bound;}
        else{_solution[i]=0;}
    }
}

uint64_t ls_solver::pick_construct_idx(int &best_value){
    return 0;
}

void ls_solver::construct_move(uint64_t var_idx, int change_value){
    
}

int ls_solver::construct_score(uint64_t var_idx,int change_value){
    return 0;
}

//basic operations
bool ls_solver::update_best_solution(){
    bool improve=false;
    if(unsat_clauses->size()<best_found_this_restart){
        improve=true;
        best_found_this_restart=unsat_clauses->size();
    }
    if(unsat_clauses->size()<best_found_cost){
        improve=true;
        best_found_cost=unsat_clauses->size();
        best_cost_time=TimeElapsed();
    }
    return improve;
}

void ls_solver::modify_CC(uint64_t var_idx, int direction){
    
}

int ls_solver::pick_critical_move(int &best_value){
    int best_score,score,best_var_idx,cnt;
    int operation_var_idx,operation_change_value,change_value;
    bool BMS=false;
    bool should_push_vec;
    best_score=0;
    best_var_idx=-1;
    change_value=0;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
    //determine the critical value
    for(int i=0;i<unsat_clauses->size();i++){
        clause *cl=&(_clauses[unsat_clauses->element_at(i)]);
        for(int l_idx:cl->literals){
            lit *l=&(_lits[std::abs(l_idx)]);
            for(int i=0;i<l->pos_coff.size();i++){
                should_push_vec=false;
                int var_idx=l->pos_coff_var_idx[i];
                if(l_idx>0&&_step>tabulist[2*var_idx+1]){
                    should_push_vec=true;
                    change_value=devide(-l->delta,l->pos_coff[i]);
                }
                else if(l_idx<0&&_step>tabulist[2*var_idx]){
                    should_push_vec=true;
                    change_value=devide(1-l->delta, l->pos_coff[i]);
                }
                if(should_push_vec){insert_operation(var_idx, change_value, operation_idx);}
                //if l_idx>0, delta should be <=0, while it is now >0(too large), so the var should enlarge by (-delta/coff) (this is a negative value), if l_idx<0, delta should be >=1, while it is now <1(too small), so the var should enlarge by (1-delta)/coff (positive value)
            }
            for(int i=0;i<l->neg_coff.size();i++){
                should_push_vec=false;
                int var_idx=l->neg_coff_var_idx[i];
                if(l_idx>0&&_step>tabulist[2*var_idx]){
                    should_push_vec=true;
                    change_value=devide(l->delta, l->neg_coff[i]);
                }
                else if(l_idx<0&&_step>tabulist[2*var_idx+1]){
                    should_push_vec=true;
                    change_value=devide(l->delta-1, l->neg_coff[i]);
                }
                if(should_push_vec){insert_operation(var_idx, change_value, operation_idx);}
                //if l_idx>0, delta should be <=0, while it is now >0(too large), so the var should enlarge by (delta/coff) (this is a positive value since the coff is neg), if l_idx<0, the delta should be >=1, while it is now <1(too small), so the var should enlarge by (delta-1)/coff (neg value)
            }
        }
    }
    //go through the forward and backward move of vars, evaluate their score, pick the untabued best one
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            operation_change_value=operation_change_value_vec[idx];
            operation_var_idx=operation_var_idx_vec[idx];
            operation_change_value_vec[idx]=operation_change_value_vec[operation_idx-i-1];
            operation_var_idx_vec[idx]=operation_var_idx_vec[operation_idx-i-1];
        }
        else{
            operation_change_value=operation_change_value_vec[i];
            operation_var_idx=operation_var_idx_vec[i];
        }
        score=critical_score(operation_var_idx,operation_change_value);
        int opposite_direction=(operation_change_value>0)?1:0;//if the change value is >0, then means it is moving forward, the opposite direction is 1(backward)
        uint64_t last_move_step=last_move[2*operation_var_idx+opposite_direction];
        if(score>best_score||(score==best_score&&last_move_step<best_last_move)){
                best_score=score;
                best_var_idx=operation_var_idx;
                best_value=operation_change_value;
                best_last_move=last_move_step;
            }
    }
    //if there is untabu decreasing move
    if(best_var_idx!=-1){return best_var_idx;}
    //TODO::choose from swap operations if there is no decreasing unsat critical
    
    //update weight and random walk
    if(mt()%10000>smooth_probability){update_clause_weight();}
    else {smooth_clause_weight();}
    random_walk();
    return -1;
}

void ls_solver::critical_move(uint64_t var_idx, int change_value){
    int direction=(change_value>0)?0:1;
    critical_score_subscore(var_idx, change_value);
    _solution[var_idx]+=change_value;
    //step
    last_move[2*var_idx+direction]=_step;
    tabulist[var_idx*2+(direction+1)%2]=_step+3+mt()%10;
    if(CC_mode!=-1){modify_CC(var_idx,direction);}
}
//transfer the ">" to "<="
void ls_solver::invert_lit(lit &l){
    l.key=1-l.key;
    std::vector<int> tmp_coff_var_idx=l.pos_coff_var_idx;
    std::vector<int> tmp_coff=l.pos_coff;
    l.pos_coff_var_idx=l.neg_coff_var_idx;
    l.pos_coff=l.neg_coff;
    l.neg_coff_var_idx=tmp_coff_var_idx;
    l.neg_coff=tmp_coff;
}
//all coffs are positive, go through all terms of the literal
int ls_solver::delta_lit(lit &l){
    int delta=l.key;
    for(int i=0;i<l.pos_coff.size();i++){delta+=(l.pos_coff[i]*_solution[l.pos_coff_var_idx[i]]);}
    for(int i=0;i<l.neg_coff.size();i++){delta-=(l.neg_coff[i]*_solution[l.neg_coff_var_idx[i]]);}
    return delta;
}

double ls_solver::TimeElapsed(){
    std::chrono::steady_clock::time_point finish = std::chrono::steady_clock::now();
    std::chrono::duration<double> duration = finish - start;
    return duration.count();
}

void ls_solver::clear_prev_data(){
    
}
//return the upper round of (a/b): (-3.5)->-4; (3.5)->4
int ls_solver::devide(int a, int b){
    int up_round=std::ceil((double)(std::abs(a))/(double)(b));
    return a>0?up_round:-up_round;
}
void ls_solver::insert_operation(int var_idx,int change_value,int &operation_idx){
    int future_solution=_solution[var_idx]+change_value;
    if(future_solution>=_vars[var_idx].low_bound&&future_solution<=_vars[var_idx].upper_bound){
        operation_var_idx_vec[operation_idx]=var_idx;
        operation_change_value_vec[operation_idx++]=change_value;
    }
}

//print
void ls_solver::print_formula(){
    for(int i=0;i<_num_clauses;i++){
        clause *cl=&(_clauses[i]);
        std::cout<<i<<"\n";
        for(int l_idx: cl->literals){
            if(l_idx<0){std::cout<<"neg: ";}
            print_literal(_lits[l_idx]);}
        std::cout<<"\n";
    }
}

void ls_solver::print_literal(lit &l){
    for(int i=0;i<l.pos_coff.size();i++)
        {std::cout<<"( "<<l.pos_coff[i]<<" * "<<_vars[l.pos_coff_var_idx[i]].var_name<<" ) + ";}
    for(int i=0;i<l.neg_coff.size();i++)
        {std::cout<<"( -"<<l.neg_coff[i]<<" * "<<_vars[l.neg_coff_var_idx[i]].var_name<<" ) + ";}
    std::cout<<"( "<<l.key<<" ) <= 0\n";
}

//calculate score
int ls_solver::critical_score(uint64_t var_idx, int change_value){
    lit *l;
    clause *cp;
    int critical_score=0;
    int delta_old,delta_new,l_clause_idx;
    //number of make_lits in a clause
    int make_break_in_clause=0;
    variable *var=&(_vars[var_idx]);
    for(int i=0;i<var->literals.size();i++){
        l=&(_lits[var->literals[i]]);
        l_clause_idx=var->literal_clause[i];
        delta_old=l->delta;
        delta_new=delta_old+(var->literal_coff[i]*change_value);//l_clause_idx means that the coff is positive, and vice versa
        if(delta_old<=0&&delta_new>0) make_break_in_clause--;
        else if(delta_old>0&&delta_new<=0) make_break_in_clause++;
        //enter a new clause or the last literal
        if( (i!=(var->literals.size()-1)&&l_clause_idx!=var->literal_clause[i+1]) ||i==(var->literals.size()-1)){
            cp=&(_clauses[std::abs(l_clause_idx)]);
            if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) critical_score+=cp->weight;
            else if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) critical_score-=cp->weight;
            make_break_in_clause=0;
        }
    }
    return critical_score;
}

int ls_solver::critical_subscore(uint64_t var_idx, int change_value){
    return 0;
}
//sat or unsat a clause, update the delta
void ls_solver::critical_score_subscore(uint64_t var_idx, int change_value){
    variable * var=&(_vars[var_idx]);
    lit *l;
    clause *cp;
    int l_clause_idx,delta_old,curr_clause_idx;
    int make_break_in_clause=0;
    for(int i=0;i<var->literals.size();i++){
        l=&(_lits[var->literals[i]]);
        l_clause_idx=var->literal_clause[i];
        delta_old=l->delta;
        l->delta=(l->delta+var->literal_coff[i]*change_value);//update the delta
        if(delta_old<=0&&l->delta>0){make_break_in_clause--;}
        else if(delta_old>0&&l->delta<=0){make_break_in_clause++;}
        //enter a new clause or the last literal
        if( (i!=(var->literals.size()-1)&&l_clause_idx!=var->literal_clause[i+1]) ||i==(var->literals.size()-1)){
            curr_clause_idx=std::abs(l_clause_idx);
            cp=&(_clauses[curr_clause_idx]);
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {
                unsat_a_clause(curr_clause_idx);//unsat clause
            }
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {
                sat_a_clause(curr_clause_idx);//sat a clause
            }
            cp->sat_count+=make_break_in_clause;
            make_break_in_clause=0;
        }
    }
}

//check
bool ls_solver::check_solution(){
    clause *cp;
    int unsat_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        bool unsat_flag=false;//false means the clause is unsat
        cp=&(_clauses[i]);
        for(int i: cp->literals){
            if(delta_lit(_lits[i])<=0){
                unsat_flag=true;//the clause is already sat
                break;
            }
        }
        if(!unsat_flag){unsat_num++;}
    }
    if(unsat_num==unsat_clauses->size())
        std::cout<<"right solution\n";
    else
        std::cout<<"wrong solution\n";
    return unsat_num==unsat_clauses->size();
}

//local search
bool ls_solver::local_search(){
    int no_improve_cnt=0;
    int flipv,change_value;
    start = std::chrono::steady_clock::now();
    initialize();
    for(_step=1;_step<_max_step;_step++){
        if(0==unsat_clauses->size()){
            check_solution();
            return true;}
        if(_step%1000==0&&(TimeElapsed()>_cutoff)){break;}
        if(no_improve_cnt>500000){initialize();no_improve_cnt=0;}//restart
        flipv=pick_critical_move(change_value);
        if(flipv!=-1){critical_move(flipv, change_value);}
        no_improve_cnt=(update_best_solution())?0:(no_improve_cnt+1);
    }
    return false;
}


}
