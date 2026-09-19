// Lean compiler output
// Module: JSP000714
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000714_memElem___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000714_isSidon(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000714_isSidon___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterTR_loop___at___00JSP000714_countSidon_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000714_countSidon(lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(lean_object* v_mask_1_, lean_object* v_e_2_){
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
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000714_memElem___boxed(lean_object* v_mask_9_, lean_object* v_e_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(v_mask_9_, v_e_10_);
lean_dec(v_e_10_);
lean_dec(v_mask_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__0(lean_object* v_i_13_, lean_object* v_j_14_, lean_object* v_k_15_, lean_object* v_mask_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 1;
return v___x_18_;
}
else
{
lean_object* v_head_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_71_; 
v_head_19_ = lean_ctor_get(v_x_17_, 0);
v_tail_20_ = lean_ctor_get(v_x_17_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_71_ == 0)
{
v___x_22_ = v_x_17_;
v_isShared_23_ = v_isSharedCheck_71_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_head_19_);
lean_dec(v_x_17_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_71_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___y_25_; lean_object* v___x_27_; lean_object* v_a_28_; lean_object* v_b_29_; lean_object* v_c_30_; lean_object* v_d_31_; lean_object* v___y_37_; lean_object* v___y_38_; uint8_t v___y_39_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_60_; uint8_t v___x_68_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v_a_28_ = lean_nat_add(v_i_13_, v___x_27_);
v_b_29_ = lean_nat_add(v_j_14_, v___x_27_);
v_c_30_ = lean_nat_add(v_k_15_, v___x_27_);
v_d_31_ = lean_nat_add(v_head_19_, v___x_27_);
lean_dec(v_head_19_);
v___x_68_ = lean_nat_dec_le(v_a_28_, v_b_29_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_inc(v_a_28_);
lean_inc(v_b_29_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_b_29_);
lean_ctor_set(v___x_69_, 1, v_a_28_);
v___y_60_ = v___x_69_;
goto v___jp_59_;
}
else
{
lean_object* v___x_70_; 
lean_inc(v_b_29_);
lean_inc(v_a_28_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_a_28_);
lean_ctor_set(v___x_70_, 1, v_b_29_);
v___y_60_ = v___x_70_;
goto v___jp_59_;
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
lean_dec(v_tail_20_);
return v___y_25_;
}
else
{
v_x_17_ = v_tail_20_;
goto _start;
}
}
v___jp_32_:
{
uint8_t v___x_33_; 
v___x_33_ = lean_nat_dec_lt(v_b_29_, v_a_28_);
lean_dec(v_a_28_);
lean_dec(v_b_29_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; 
v___x_34_ = lean_nat_dec_lt(v_d_31_, v_c_30_);
lean_dec(v_c_30_);
lean_dec(v_d_31_);
v___y_25_ = v___x_34_;
goto v___jp_24_;
}
else
{
lean_dec(v_d_31_);
lean_dec(v_c_30_);
v_x_17_ = v_tail_20_;
goto _start;
}
}
v___jp_36_:
{
if (v___y_39_ == 0)
{
lean_dec_ref(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v_d_31_);
lean_dec(v_c_30_);
lean_dec(v_b_29_);
lean_dec(v_a_28_);
v_x_17_ = v_tail_20_;
goto _start;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(v_mask_16_, v_c_30_);
if (v___x_41_ == 0)
{
lean_dec_ref(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v_d_31_);
lean_dec(v_c_30_);
lean_dec(v_b_29_);
lean_dec(v_a_28_);
v_x_17_ = v_tail_20_;
goto _start;
}
else
{
uint8_t v___x_43_; 
v___x_43_ = lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(v_mask_16_, v_d_31_);
if (v___x_43_ == 0)
{
lean_dec_ref(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v_d_31_);
lean_dec(v_c_30_);
lean_dec(v_b_29_);
lean_dec(v_a_28_);
v___y_25_ = v___x_41_;
goto v___jp_24_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_44_ = lean_nat_add(v_a_28_, v_b_29_);
v___x_45_ = lean_nat_add(v_c_30_, v_d_31_);
v___x_46_ = lean_nat_dec_eq(v___x_44_, v___x_45_);
lean_dec(v___x_45_);
lean_dec(v___x_44_);
if (v___x_46_ == 0)
{
lean_dec_ref(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v_d_31_);
lean_dec(v_c_30_);
lean_dec(v_b_29_);
lean_dec(v_a_28_);
v___y_25_ = v___x_43_;
goto v___jp_24_;
}
else
{
lean_object* v_fst_47_; lean_object* v_snd_48_; lean_object* v_fst_49_; lean_object* v_snd_50_; uint8_t v___x_51_; 
v_fst_47_ = lean_ctor_get(v___y_37_, 0);
lean_inc(v_fst_47_);
v_snd_48_ = lean_ctor_get(v___y_37_, 1);
lean_inc(v_snd_48_);
lean_dec_ref(v___y_37_);
v_fst_49_ = lean_ctor_get(v___y_38_, 0);
lean_inc(v_fst_49_);
v_snd_50_ = lean_ctor_get(v___y_38_, 1);
lean_inc(v_snd_50_);
lean_dec_ref(v___y_38_);
v___x_51_ = lean_nat_dec_eq(v_fst_47_, v_fst_49_);
lean_dec(v_fst_49_);
lean_dec(v_fst_47_);
if (v___x_51_ == 0)
{
lean_dec(v_snd_50_);
lean_dec(v_snd_48_);
goto v___jp_32_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = lean_nat_dec_eq(v_snd_48_, v_snd_50_);
lean_dec(v_snd_50_);
lean_dec(v_snd_48_);
if (v___x_52_ == 0)
{
goto v___jp_32_;
}
else
{
lean_dec(v_d_31_);
lean_dec(v_c_30_);
lean_dec(v_b_29_);
lean_dec(v_a_28_);
v_x_17_ = v_tail_20_;
goto _start;
}
}
}
}
}
}
}
v___jp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(v_mask_16_, v_a_28_);
if (v___x_57_ == 0)
{
v___y_37_ = v___y_55_;
v___y_38_ = v___y_56_;
v___y_39_ = v___x_57_;
goto v___jp_36_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = lp_jsp_x2dlean_x2dproofs_JSP000714_memElem(v_mask_16_, v_b_29_);
v___y_37_ = v___y_55_;
v___y_38_ = v___y_56_;
v___y_39_ = v___x_58_;
goto v___jp_36_;
}
}
v___jp_59_:
{
uint8_t v___x_61_; 
v___x_61_ = lean_nat_dec_le(v_c_30_, v_d_31_);
if (v___x_61_ == 0)
{
lean_object* v___x_63_; 
lean_inc(v_c_30_);
lean_inc(v_d_31_);
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 0);
lean_ctor_set(v___x_22_, 1, v_c_30_);
lean_ctor_set(v___x_22_, 0, v_d_31_);
v___x_63_ = v___x_22_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_d_31_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_c_30_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
v___y_55_ = v___y_60_;
v___y_56_ = v___x_63_;
goto v___jp_54_;
}
}
else
{
lean_object* v___x_66_; 
lean_inc(v_d_31_);
lean_inc(v_c_30_);
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 0);
lean_ctor_set(v___x_22_, 1, v_d_31_);
lean_ctor_set(v___x_22_, 0, v_c_30_);
v___x_66_ = v___x_22_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_c_30_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_d_31_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
v___y_55_ = v___y_60_;
v___y_56_ = v___x_66_;
goto v___jp_54_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__0___boxed(lean_object* v_i_72_, lean_object* v_j_73_, lean_object* v_k_74_, lean_object* v_mask_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__0(v_i_72_, v_j_73_, v_k_74_, v_mask_75_, v_x_76_);
lean_dec(v_mask_75_);
lean_dec(v_k_74_);
lean_dec(v_j_73_);
lean_dec(v_i_72_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__1(lean_object* v_i_79_, lean_object* v_j_80_, lean_object* v_mask_81_, lean_object* v___x_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
uint8_t v___x_84_; 
lean_dec(v___x_82_);
v___x_84_ = 1;
return v___x_84_;
}
else
{
lean_object* v_head_85_; lean_object* v_tail_86_; uint8_t v___x_87_; 
v_head_85_ = lean_ctor_get(v_x_83_, 0);
v_tail_86_ = lean_ctor_get(v_x_83_, 1);
lean_inc(v___x_82_);
v___x_87_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__0(v_i_79_, v_j_80_, v_head_85_, v_mask_81_, v___x_82_);
if (v___x_87_ == 0)
{
lean_dec(v___x_82_);
return v___x_87_;
}
else
{
v_x_83_ = v_tail_86_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__1___boxed(lean_object* v_i_89_, lean_object* v_j_90_, lean_object* v_mask_91_, lean_object* v___x_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__1(v_i_89_, v_j_90_, v_mask_91_, v___x_92_, v_x_93_);
lean_dec(v_x_93_);
lean_dec(v_mask_91_);
lean_dec(v_j_90_);
lean_dec(v_i_89_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__2(lean_object* v_i_96_, lean_object* v_mask_97_, lean_object* v___x_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
uint8_t v___x_100_; 
lean_dec(v___x_98_);
v___x_100_ = 1;
return v___x_100_;
}
else
{
lean_object* v_head_101_; lean_object* v_tail_102_; uint8_t v___x_103_; 
v_head_101_ = lean_ctor_get(v_x_99_, 0);
v_tail_102_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v___x_98_);
v___x_103_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__1(v_i_96_, v_head_101_, v_mask_97_, v___x_98_, v___x_98_);
if (v___x_103_ == 0)
{
lean_dec(v___x_98_);
return v___x_103_;
}
else
{
v_x_99_ = v_tail_102_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__2___boxed(lean_object* v_i_105_, lean_object* v_mask_106_, lean_object* v___x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__2(v_i_105_, v_mask_106_, v___x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v_mask_106_);
lean_dec(v_i_105_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__3(lean_object* v_mask_111_, lean_object* v___x_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
uint8_t v___x_114_; 
lean_dec(v___x_112_);
v___x_114_ = 1;
return v___x_114_;
}
else
{
lean_object* v_head_115_; lean_object* v_tail_116_; uint8_t v___x_117_; 
v_head_115_ = lean_ctor_get(v_x_113_, 0);
v_tail_116_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v___x_112_);
v___x_117_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__2(v_head_115_, v_mask_111_, v___x_112_, v___x_112_);
if (v___x_117_ == 0)
{
lean_dec(v___x_112_);
return v___x_117_;
}
else
{
v_x_113_ = v_tail_116_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__3___boxed(lean_object* v_mask_119_, lean_object* v___x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__3(v_mask_119_, v___x_120_, v_x_121_);
lean_dec(v_x_121_);
lean_dec(v_mask_119_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2dlean_x2dproofs_JSP000714_isSidon(lean_object* v_n_124_, lean_object* v_mask_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = l_List_range(v_n_124_);
lean_inc(v___x_126_);
v___x_127_ = lp_jsp_x2dlean_x2dproofs_List_all___at___00JSP000714_isSidon_spec__3(v_mask_125_, v___x_126_, v___x_126_);
lean_dec(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000714_isSidon___boxed(lean_object* v_n_128_, lean_object* v_mask_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = lp_jsp_x2dlean_x2dproofs_JSP000714_isSidon(v_n_128_, v_mask_129_);
lean_dec(v_mask_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_List_filterTR_loop___at___00JSP000714_countSidon_spec__0(lean_object* v_n_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
if (lean_obj_tag(v_a_133_) == 0)
{
lean_object* v___x_135_; 
lean_dec(v_n_132_);
v___x_135_ = l_List_reverse___redArg(v_a_134_);
return v___x_135_;
}
else
{
lean_object* v_head_136_; lean_object* v_tail_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
v_head_136_ = lean_ctor_get(v_a_133_, 0);
v_tail_137_ = lean_ctor_get(v_a_133_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_a_133_);
if (v_isSharedCheck_147_ == 0)
{
v___x_139_ = v_a_133_;
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_tail_137_);
lean_inc(v_head_136_);
lean_dec(v_a_133_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint8_t v___x_141_; 
lean_inc(v_n_132_);
v___x_141_ = lp_jsp_x2dlean_x2dproofs_JSP000714_isSidon(v_n_132_, v_head_136_);
if (v___x_141_ == 0)
{
lean_del_object(v___x_139_);
lean_dec(v_head_136_);
v_a_133_ = v_tail_137_;
goto _start;
}
else
{
lean_object* v___x_144_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v_a_134_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_head_136_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_a_134_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v_a_133_ = v_tail_137_;
v_a_134_ = v___x_144_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_jsp_x2dlean_x2dproofs_JSP000714_countSidon(lean_object* v_n_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_149_ = lean_unsigned_to_nat(2u);
v___x_150_ = lean_nat_pow(v___x_149_, v_n_148_);
v___x_151_ = l_List_range(v___x_150_);
v___x_152_ = lean_box(0);
v___x_153_ = lp_jsp_x2dlean_x2dproofs_List_filterTR_loop___at___00JSP000714_countSidon_spec__0(v_n_148_, v___x_151_, v___x_152_);
v___x_154_ = l_List_lengthTR___redArg(v___x_153_);
lean_dec(v___x_153_);
return v___x_154_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_List_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_jsp_x2dlean_x2dproofs_JSP000714(uint8_t builtin) {
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
