/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000419: What is the typical maximum modulus on the unit
circle of a polynomial with random sign coefficients?

The research problem (Kahane-style) studies the a.s. growth of
`max_{|z|=1} |∑ ε_k z^k|` for random signs `ε_k = ±1`.  We formalize the
quantity for a fixed sign pattern — the supremum of the modulus over the
unit circle — and evaluate it exactly in a machine-checked bounded instance:

For the sign pattern `(1, -1, 1)`, i.e. `P(z) = 1 - z + z²`, the maximum of
`|P|` on the unit circle is exactly `3`: the triangle inequality gives
`|P(z)| ≤ |1| + |z| + |z|² = 3` for every `|z| = 1`, and the bound is
attained at `z = -1` where `P(-1) = 3`.  So the supremum equals the
triangle-inequality upper bound in this case.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace JSP000419

open Metric

/-- The sign polynomial with coefficient pattern `(1, -1, 1)`. -/
noncomputable def P (z : ℂ) : ℂ := 1 - z + z ^ 2

/-- Triangle-inequality upper bound on the unit circle. -/
theorem upper_bound (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : ‖P z‖ ≤ 3 := by
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have h1 : ‖P z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ + ‖z‖ ^ 2 := by
    refine le_trans (norm_add_le _ _) ?_
    exact add_le_add (norm_sub_le _ _) (norm_pow _ _).le
  rw [norm_one, hz1] at h1
  norm_num at h1
  exact h1

/-- The supremum of `|P|` over the unit circle is exactly `3`. -/
theorem jsp_000419 :
    sSup ((fun z => ‖P z‖) '' sphere (0:ℂ) 1) = 3 := by
  have hm1 : (-1 : ℂ) ∈ sphere (0:ℂ) 1 := mem_sphere_zero_iff_norm.mpr (by norm_num)
  have hP3 : P (-1) = 3 := by norm_num [P]
  have hne : ((fun z => ‖P z‖) '' sphere (0:ℂ) 1).Nonempty :=
    ⟨‖P (-1)‖, ⟨-1, hm1, rfl⟩⟩
  have hbd : BddAbove ((fun z => ‖P z‖) '' sphere (0:ℂ) 1) :=
    ⟨3, fun b hb => by obtain ⟨z, hz, rfl⟩ := hb; exact upper_bound z hz⟩
  refine le_antisymm (csSup_le hne fun b hb => ?_) (le_csSup hbd ?_)
  · obtain ⟨z, hz, rfl⟩ := hb
    exact upper_bound z hz
  · exact ⟨-1, hm1, by show ‖P (-1)‖ = 3; rw [hP3]; norm_num⟩

end JSP000419
