// Lean compiler output
// Module: JSP000589
// Imports: public import Init public meta import Init public import Mathlib.Tactic.IntervalCases public import Mathlib.Data.List.Basic
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000589_color(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_color___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterMapTR_go___at___00JSP000589_apPairs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterMapTR_go___at___00JSP000589_apPairs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1___closed__0 = (const lean_object*)&lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_apPairs(lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000589_isMono3AP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_isMono3AP___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_any___at___00JSP000589_hasMono3APLen_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_any___at___00JSP000589_hasMono3APLen_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000589_hasMono3APLen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_hasMono3APLen___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000589_color(lean_object* v_n_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_3_ = lean_nat_shiftr(v_n_1_, v_i_2_);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_mod(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_dec_eq(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_color___boxed(lean_object* v_n_8_, lean_object* v_i_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_jsp_x2dlean_x2dproofs_JSP000589_color(v_n_8_, v_i_9_);
lean_dec(v_i_9_);
lean_dec(v_n_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterMapTR_go___at___00JSP000589_apPairs_spec__0(lean_object* v_a_12_, lean_object* v_k_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
if (lean_obj_tag(v_a_14_) == 0)
{
lean_object* v___x_16_; 
lean_dec(v_a_12_);
v___x_16_ = lean_array_to_list(v_a_15_);
return v___x_16_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_35_; 
v_head_17_ = lean_ctor_get(v_a_14_, 0);
v_tail_18_ = lean_ctor_get(v_a_14_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_a_14_);
if (v_isSharedCheck_35_ == 0)
{
v___x_20_ = v_a_14_;
v_isShared_21_ = v_isSharedCheck_35_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_head_17_);
lean_dec(v_a_14_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_35_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
uint8_t v___y_23_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_lt(v___x_30_, v_head_17_);
if (v___x_31_ == 0)
{
v___y_23_ = v___x_31_;
goto v___jp_22_;
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_32_ = lean_nat_add(v_a_12_, v_head_17_);
v___x_33_ = lean_nat_add(v___x_32_, v_head_17_);
lean_dec(v___x_32_);
v___x_34_ = lean_nat_dec_lt(v___x_33_, v_k_13_);
lean_dec(v___x_33_);
v___y_23_ = v___x_34_;
goto v___jp_22_;
}
v___jp_22_:
{
if (v___y_23_ == 0)
{
lean_del_object(v___x_20_);
lean_dec(v_head_17_);
v_a_14_ = v_tail_18_;
goto _start;
}
else
{
lean_object* v___x_26_; 
lean_inc(v_a_12_);
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 0);
lean_ctor_set(v___x_20_, 1, v_head_17_);
lean_ctor_set(v___x_20_, 0, v_a_12_);
v___x_26_ = v___x_20_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_12_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_head_17_);
v___x_26_ = v_reuseFailAlloc_29_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; 
v___x_27_ = lean_array_push(v_a_15_, v___x_26_);
v_a_14_ = v_tail_18_;
v_a_15_ = v___x_27_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterMapTR_go___at___00JSP000589_apPairs_spec__0___boxed(lean_object* v_a_36_, lean_object* v_k_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_jsp_x2dlean_x2dproofs_List_filterMapTR_go___at___00JSP000589_apPairs_spec__0(v_a_36_, v_k_37_, v_a_38_, v_a_39_);
lean_dec(v_k_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1(lean_object* v_k_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
if (lean_obj_tag(v_a_44_) == 0)
{
lean_object* v___x_46_; 
lean_dec(v_k_43_);
v___x_46_ = lean_array_to_list(v_a_45_);
return v___x_46_;
}
else
{
lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_head_47_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_head_47_);
v_tail_48_ = lean_ctor_get(v_a_44_, 1);
lean_inc(v_tail_48_);
lean_dec_ref_known(v_a_44_, 2);
lean_inc(v_k_43_);
v___x_49_ = l_List_range(v_k_43_);
v___x_50_ = ((lean_object*)(lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1___closed__0));
v___x_51_ = lp_jsp_x2dlean_x2dproofs_List_filterMapTR_go___at___00JSP000589_apPairs_spec__0(v_head_47_, v_k_43_, v___x_49_, v___x_50_);
v___x_52_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_45_, v___x_51_);
v_a_44_ = v_tail_48_;
v_a_45_ = v___x_52_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_apPairs(lean_object* v_k_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_inc(v_k_54_);
v___x_55_ = l_List_range(v_k_54_);
v___x_56_ = ((lean_object*)(lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1___closed__0));
v___x_57_ = lp_jsp_x2dlean_x2dproofs___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00JSP000589_apPairs_spec__1(v_k_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000589_isMono3AP(lean_object* v_n_58_, lean_object* v_p_59_){
_start:
{
lean_object* v_fst_60_; lean_object* v_snd_61_; uint8_t v___y_63_; uint8_t v___y_69_; uint8_t v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_fst_60_ = lean_ctor_get(v_p_59_, 0);
v_snd_61_ = lean_ctor_get(v_p_59_, 1);
v___x_70_ = lp_jsp_x2dlean_x2dproofs_JSP000589_color(v_n_58_, v_fst_60_);
v___x_71_ = lean_nat_add(v_fst_60_, v_snd_61_);
v___x_72_ = lp_jsp_x2dlean_x2dproofs_JSP000589_color(v_n_58_, v___x_71_);
lean_dec(v___x_71_);
if (v___x_72_ == 0)
{
if (v___x_70_ == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 1;
v___y_63_ = v___x_73_;
goto v___jp_62_;
}
else
{
v___y_69_ = v___x_72_;
goto v___jp_68_;
}
}
else
{
v___y_69_ = v___x_70_;
goto v___jp_68_;
}
v___jp_62_:
{
lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_64_ = lean_nat_add(v_fst_60_, v_snd_61_);
v___x_65_ = lp_jsp_x2dlean_x2dproofs_JSP000589_color(v_n_58_, v___x_64_);
v___x_66_ = lean_nat_add(v___x_64_, v_snd_61_);
lean_dec(v___x_64_);
v___x_67_ = lp_jsp_x2dlean_x2dproofs_JSP000589_color(v_n_58_, v___x_66_);
lean_dec(v___x_66_);
if (v___x_67_ == 0)
{
if (v___x_65_ == 0)
{
return v___y_63_;
}
else
{
return v___x_67_;
}
}
else
{
return v___x_65_;
}
}
v___jp_68_:
{
if (v___y_69_ == 0)
{
return v___y_69_;
}
else
{
v___y_63_ = v___y_69_;
goto v___jp_62_;
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_isMono3AP___boxed(lean_object* v_n_74_, lean_object* v_p_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = lp_jsp_x2dlean_x2dproofs_JSP000589_isMono3AP(v_n_74_, v_p_75_);
lean_dec_ref(v_p_75_);
lean_dec(v_n_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_any___at___00JSP000589_hasMono3APLen_spec__0(lean_object* v_n_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; uint8_t v___x_83_; 
v_head_81_ = lean_ctor_get(v_x_79_, 0);
v_tail_82_ = lean_ctor_get(v_x_79_, 1);
v___x_83_ = lp_jsp_x2dlean_x2dproofs_JSP000589_isMono3AP(v_n_78_, v_head_81_);
if (v___x_83_ == 0)
{
v_x_79_ = v_tail_82_;
goto _start;
}
else
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_any___at___00JSP000589_hasMono3APLen_spec__0___boxed(lean_object* v_n_85_, lean_object* v_x_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = lp_jsp_x2dlean_x2dproofs_List_any___at___00JSP000589_hasMono3APLen_spec__0(v_n_85_, v_x_86_);
lean_dec(v_x_86_);
lean_dec(v_n_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000589_hasMono3APLen(lean_object* v_n_89_, lean_object* v_k_90_){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lp_jsp_x2dlean_x2dproofs_JSP000589_apPairs(v_k_90_);
v___x_92_ = lp_jsp_x2dlean_x2dproofs_List_any___at___00JSP000589_hasMono3APLen_spec__0(v_n_89_, v___x_91_);
lean_dec(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000589_hasMono3APLen___boxed(lean_object* v_n_93_, lean_object* v_k_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = lp_jsp_x2dlean_x2dproofs_JSP000589_hasMono3APLen(v_n_93_, v_k_94_);
lean_dec(v_n_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_IntervalCases(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_List_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_jsp_x2dlean_x2dproofs_JSP000589(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Tactic_IntervalCases(builtin);
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
