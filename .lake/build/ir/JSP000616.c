// Lean compiler output
// Module: JSP000616
// Imports: public import Init public meta import Init public import Mathlib.Data.List.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000616_memElem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000616_memElem___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000616_isSumFree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000616_isSumFree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterTR_loop___at___00JSP000616_countSumFree_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000616_countSumFree(lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000616_memElem(lean_object* v_mask_1_, lean_object* v_e_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_sub(v_e_2_, v___x_3_);
v___x_5_ = lean_nat_shiftr(v_mask_1_, v___x_4_);
lean_dec(v___x_4_);
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = lean_nat_mod(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_nat_dec_eq(v___x_7_, v___x_3_);
lean_dec(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000616_memElem___boxed(lean_object* v_mask_9_, lean_object* v_e_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_jsp_x2dlean_x2dproofs_JSP000616_memElem(v_mask_9_, v_e_10_);
lean_dec(v_e_10_);
lean_dec(v_mask_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__0(lean_object* v_x_13_, lean_object* v_n_14_, lean_object* v_mask_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
uint8_t v___x_17_; 
v___x_17_ = 1;
return v___x_17_;
}
else
{
lean_object* v_head_18_; lean_object* v_tail_19_; lean_object* v___x_20_; lean_object* v_a_21_; lean_object* v_b_22_; lean_object* v_c_23_; uint8_t v___x_24_; uint8_t v___y_26_; 
v_head_18_ = lean_ctor_get(v_x_16_, 0);
v_tail_19_ = lean_ctor_get(v_x_16_, 1);
v___x_20_ = lean_unsigned_to_nat(1u);
v_a_21_ = lean_nat_add(v_x_13_, v___x_20_);
v_b_22_ = lean_nat_add(v_head_18_, v___x_20_);
v_c_23_ = lean_nat_add(v_a_21_, v_b_22_);
v___x_24_ = lean_nat_dec_lt(v_n_14_, v_c_23_);
if (v___x_24_ == 0)
{
uint8_t v___x_31_; 
v___x_31_ = lp_jsp_x2dlean_x2dproofs_JSP000616_memElem(v_mask_15_, v_a_21_);
lean_dec(v_a_21_);
if (v___x_31_ == 0)
{
lean_dec(v_b_22_);
v___y_26_ = v___x_31_;
goto v___jp_25_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = lp_jsp_x2dlean_x2dproofs_JSP000616_memElem(v_mask_15_, v_b_22_);
lean_dec(v_b_22_);
v___y_26_ = v___x_32_;
goto v___jp_25_;
}
}
else
{
lean_dec(v_c_23_);
lean_dec(v_b_22_);
lean_dec(v_a_21_);
v_x_16_ = v_tail_19_;
goto _start;
}
v___jp_25_:
{
if (v___y_26_ == 0)
{
lean_dec(v_c_23_);
v_x_16_ = v_tail_19_;
goto _start;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lp_jsp_x2dlean_x2dproofs_JSP000616_memElem(v_mask_15_, v_c_23_);
lean_dec(v_c_23_);
if (v___x_28_ == 0)
{
v_x_16_ = v_tail_19_;
goto _start;
}
else
{
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
v_x_16_ = v_tail_19_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__0___boxed(lean_object* v_x_34_, lean_object* v_n_35_, lean_object* v_mask_36_, lean_object* v_x_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__0(v_x_34_, v_n_35_, v_mask_36_, v_x_37_);
lean_dec(v_x_37_);
lean_dec(v_mask_36_);
lean_dec(v_n_35_);
lean_dec(v_x_34_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__1(lean_object* v_n_40_, lean_object* v_mask_41_, lean_object* v___x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
uint8_t v___x_44_; 
v___x_44_ = 1;
return v___x_44_;
}
else
{
lean_object* v_head_45_; lean_object* v_tail_46_; uint8_t v___x_47_; 
v_head_45_ = lean_ctor_get(v_x_43_, 0);
v_tail_46_ = lean_ctor_get(v_x_43_, 1);
v___x_47_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__0(v_head_45_, v_n_40_, v_mask_41_, v___x_42_);
if (v___x_47_ == 0)
{
return v___x_47_;
}
else
{
v_x_43_ = v_tail_46_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__1___boxed(lean_object* v_n_49_, lean_object* v_mask_50_, lean_object* v___x_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__1(v_n_49_, v_mask_50_, v___x_51_, v_x_52_);
lean_dec(v_x_52_);
lean_dec(v___x_51_);
lean_dec(v_mask_50_);
lean_dec(v_n_49_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000616_isSumFree(lean_object* v_n_55_, lean_object* v_mask_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
lean_inc(v_n_55_);
v___x_57_ = l_List_range(v_n_55_);
v___x_58_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000616_isSumFree_spec__1(v_n_55_, v_mask_56_, v___x_57_, v___x_57_);
lean_dec(v___x_57_);
lean_dec(v_n_55_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000616_isSumFree___boxed(lean_object* v_n_59_, lean_object* v_mask_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = lp_jsp_x2dlean_x2dproofs_JSP000616_isSumFree(v_n_59_, v_mask_60_);
lean_dec(v_mask_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterTR_loop___at___00JSP000616_countSumFree_spec__0(lean_object* v_n_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
if (lean_obj_tag(v_a_64_) == 0)
{
lean_object* v___x_66_; 
lean_dec(v_n_63_);
v___x_66_ = l_List_reverse___redArg(v_a_65_);
return v___x_66_;
}
else
{
lean_object* v_head_67_; lean_object* v_tail_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_78_; 
v_head_67_ = lean_ctor_get(v_a_64_, 0);
v_tail_68_ = lean_ctor_get(v_a_64_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_78_ == 0)
{
v___x_70_ = v_a_64_;
v_isShared_71_ = v_isSharedCheck_78_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_tail_68_);
lean_inc(v_head_67_);
lean_dec(v_a_64_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_78_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
lean_inc(v_n_63_);
v___x_72_ = lp_jsp_x2dlean_x2dproofs_JSP000616_isSumFree(v_n_63_, v_head_67_);
if (v___x_72_ == 0)
{
lean_del_object(v___x_70_);
lean_dec(v_head_67_);
v_a_64_ = v_tail_68_;
goto _start;
}
else
{
lean_object* v___x_75_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v_a_65_);
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_head_67_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_a_65_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
v_a_64_ = v_tail_68_;
v_a_65_ = v___x_75_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000616_countSumFree(lean_object* v_n_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_pow(v___x_80_, v_n_79_);
v___x_82_ = l_List_range(v___x_81_);
v___x_83_ = lean_box(0);
v___x_84_ = lp_jsp_x2dlean_x2dproofs_List_filterTR_loop___at___00JSP000616_countSumFree_spec__0(v_n_79_, v___x_82_, v___x_83_);
v___x_85_ = l_List_lengthTR___redArg(v___x_84_);
lean_dec(v___x_84_);
return v___x_85_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_List_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_jsp_x2dlean_x2dproofs_JSP000616(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
