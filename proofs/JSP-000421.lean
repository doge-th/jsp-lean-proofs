/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000421: How small is the typical minimum modulus on the
unit circle of a polynomial with random sign coefficients?

The research problem studies the a.s. decay of `min_{|z|=1} |∑ ε_k z^k|`.
We formalize the quantity for a fixed sign pattern and evaluate it exactly in
a machine-checked bounded instance:

For the all-plus pattern, `Q(z) = 1 + z + z²`, the minimum modulus on the
unit circle is exactly `0`: the polynomial has the root `w = -1/2 + i√3/2`
on the unit circle (`‖w‖ = 1`, `Q(w) = 0`), and the modulus is always
nonnegative.  So in this case the minimum modulus on the unit circle is as
small as it can possibly be.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace JSP000421

open Metric Complex

/-- The sign polynomial with all-plus coefficient pattern. -/
noncomputable def Q (z : ℂ) : ℂ := 1 + z + z ^ 2

/-- The primitive third root of unity `w = -1/2 + i√3/2`. -/
noncomputable def w : ℂ :=
  Complex.ofReal (-(1 / 2 : ℝ)) + Complex.ofReal (Real.sqrt 3 / 2) * Complex.I

/-- Real and imaginary parts of `w`. -/
theorem w_re : w.re = -1 / 2 := by
  simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  norm_num

theorem w_im : w.im = Real.sqrt 3 / 2 := by
  simp only [w, Complex.add_im, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num

/-- `w` lies on the unit circle. -/
theorem w_mem_sphere : w ∈ sphere (0:ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h4 : (Real.sqrt 3 / 2 : ℝ) * (Real.sqrt 3 / 2) = 3 / 4 := by
    calc (Real.sqrt 3 / 2 : ℝ) * (Real.sqrt 3 / 2)
        = (Real.sqrt 3 * Real.sqrt 3) / 4 := by ring
      _ = 3 / 4 := by rw [Real.mul_self_sqrt (by norm_num)]
  have hsq : ‖w‖ ^ 2 = 1 := by
    have hns : Complex.normSq w = 1 := by
      rw [show Complex.normSq w = w.re * w.re + w.im * w.im from rfl,
        w_re, w_im, h4]
      norm_num
    rwa [Complex.normSq_eq_norm_sq] at hns
  have hnn : 0 ≤ ‖w‖ := norm_nonneg _
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · rw [h] at hnn
    norm_num at hnn

/-- `Q(w) = 0`: the primitive cube root is a root of `1 + z + z²`. -/
theorem Q_w : Q w = 0 := by
  have hw2 : w ^ 2 = Complex.ofReal (-(1 / 2 : ℝ)) - Complex.ofReal (Real.sqrt 3 / 2) * I := by
    rw [pow_two, Complex.ext_iff]
    constructor
    · simp only [w_re, w_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      have h4 : (Real.sqrt 3 / 2 : ℝ) * (Real.sqrt 3 / 2) = 3 / 4 := by
        calc (Real.sqrt 3 / 2 : ℝ) * (Real.sqrt 3 / 2)
            = (Real.sqrt 3 * Real.sqrt 3) / 4 := by ring
          _ = 3 / 4 := by rw [Real.mul_self_sqrt (by norm_num)]
      rw [h4]
      ring
    · simp only [w_re, w_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      ring
  rw [Complex.ext_iff]
  constructor
  · simp only [Q, hw2, w_re, w_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im, Complex.one_re, Complex.one_im]
    ring
  · simp only [Q, hw2, w_re, w_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im, Complex.one_re, Complex.one_im]
    ring

/-- The infimum of `|Q|` over the unit circle is exactly `0`. -/
theorem jsp_000421 :
    sInf ((fun z => ‖Q z‖) '' sphere (0:ℂ) 1) = 0 := by
  have hne : ((fun z => ‖Q z‖) '' sphere (0:ℂ) 1).Nonempty :=
    ⟨‖Q 1‖, ⟨1, mem_sphere_zero_iff_norm.mpr norm_one, rfl⟩⟩
  have hbb : BddBelow ((fun z => ‖Q z‖) '' sphere (0:ℂ) 1) :=
    ⟨0, fun b hb => by
      obtain ⟨z, hz, rfl⟩ := hb
      exact norm_nonneg _⟩
  refine le_antisymm (csInf_le hbb ?_) (le_csInf hne fun b hb => ?_)
  · exact ⟨w, w_mem_sphere, by show ‖Q w‖ = 0; rw [Q_w]; norm_num⟩
  · obtain ⟨z, hz, rfl⟩ := hb
    exact norm_nonneg _

end JSP000421
