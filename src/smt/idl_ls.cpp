#include "smt/idl_ls.h"
using namespace boolidl;
bool_ls_solver::bool_ls_solver(){
    _additional_len=10;
    _max_tries=1;
    _max_step=UINT64_MAX;
    _swt_p=0.7;
    _swt_threshold=50;
    smooth_probability=3;
}