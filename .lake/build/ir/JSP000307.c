// Lean compiler output
// Module: JSP000307
// Imports: public import Init public meta import Init public import Mathlib.Data.Nat.MaxPrimeFac
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_mathlib_Nat_maxPrimeFac(lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000307_largestPrimeFactor(lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000307_largestPrimeFactor___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000307_largestPrimeFactor(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_Nat_maxPrimeFac(v_n_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000307_largestPrimeFactor___boxed(lean_object* v_n_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_jsp_x2dlean_x2dproofs_JSP000307_largestPrimeFactor(v_n_3_);
lean_dec(v_n_3_);
return v_res_4_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_MaxPrimeFac(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_jsp_x2dlean_x2dproofs_JSP000307(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_MaxPrimeFac(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
