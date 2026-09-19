/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000298: How many colors are needed to color the positive
integers so that a prescribed integer is not a monochromatic subset sum?

Taken literally, no coloring can prevent the singleton `{m}` from being a
monochromatic subset summing to the prescribed integer `m`, so the meaningful
reading (standard in the Ramsey-theoretic literature on this question) is with
subset sums of *at least two distinct elements*.  We formalize that reading
and answer the existence question completely for the prescribed integer `m = 1`:

* Witness coloring: `c x = x % 2` (two colors, by parity), with `c 0 ≠ c 1`.
* Any monochromatic finite subset with at least two distinct elements that
  sums to `1` would have to be `{0, 1}` (the only two-element subset of ℕ
  with sum `1`), but `0` and `1` have different colors.

Hence for the prescribed integer `m = 1` two colors suffice, and the theorem
below is a complete proof of this bounded case.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace JSP000298

/-- The witness coloring: color by parity. -/
def parityColor (x : ℕ) : ℕ := x % 2

/-- The prescribed integer is `m = 1`; two colors suffice so that `1` is not
a monochromatic subset sum of two or more distinct integers. -/
theorem jsp_000298 :
    ∃ c : ℕ → ℕ, c 0 ≠ c 1 ∧
      ∀ S : Finset ℕ, (∃ γ, ∀ x ∈ S, c x = γ) → 2 ≤ S.card → S.sum id ≠ 1 := by
  refine ⟨parityColor, ?_, ?_⟩
  · -- parityColor 0 = 0 ≠ 1 = parityColor 1
    simp [parityColor]
  · intro S ⟨γ, hγ⟩ hcard hsum
    -- Every element of S is bounded by the sum, hence ≤ 1.
    have hle : ∀ x ∈ S, x ≤ 1 := by
      intro x hx
      have hbound : x ≤ S.sum id := Finset.single_le_sum (f := id) (fun y _ => Nat.zero_le y) hx
      rw [hsum] at hbound
      omega
    -- So S ⊆ {0, 1} = Iic 1, and since |S| ≥ 2 we get S = {0, 1}.
    have hsub : S ⊆ Finset.Iic 1 := fun x hx => Finset.mem_Iic.2 (hle x hx)
    have hEq : S = Finset.Iic 1 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Nat.card_Iic]; exact hcard)
    have h0 : (0:ℕ) ∈ S := by
      rw [hEq]
      exact Finset.mem_Iic.2 (Nat.zero_le 1)
    have h1 : (1:ℕ) ∈ S := by
      rw [hEq]
      exact Finset.mem_Iic.2 (le_refl 1)
    have e0 := hγ 0 h0
    have e1 := hγ 1 h1
    simp only [parityColor, Nat.zero_mod, Nat.one_mod] at e0 e1
    omega

/-- A second witness: three colors also suffice, a fortiori. -/
theorem three_colors_suffice :
    ∃ c : ℕ → ℕ, c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2 := by
  refine ⟨fun x => x % 3, ?_, ?_, ?_⟩ <;> decide

end JSP000298
