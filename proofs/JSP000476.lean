/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000476: How large can a subset of an integer interval be
if none of its nonempty subset sums is a square?

Lower-bound witness: inside the interval `[1, 192]`, the 5-element set
`{3, 8, 12, 48, 192}` has no nonempty subset whose element sum is a perfect
square: its 31 nonempty subset sums

  3, 8, 11, 12, 15, 20, 23, 48, 51, 56, 59, 60, 63, 68, 71,
  192, 195, 200, 203, 204, 207, 212, 215, 240, 243, 248, 251, 252, 255,
  260, 263

avoid the squares 1, 4, 9, 16, 25, 36, 49, 64, 196, 225, 256.  (Appending
`4 · max` to such a set preserves the property whenever `4 · max` skips the
next squares, so large intervals admit large such subsets.)
-/

import Mathlib.Data.Nat.MaxPrimeFac
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped BigOperators

namespace JSP000476

/-- JSP-000476: a 5-element square-subset-sum-free subset of `[1, 192]`. -/
theorem jsp_000476 :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 192 ∧ S.card = 5 ∧
      ∀ T ∈ S.powerset, T = ∅ ∨ (Nat.sqrt (∑ x ∈ T, x)) ^ 2 ≠ ∑ x ∈ T, x := by
  refine ⟨{3, 8, 12, 48, 192}, ?_, by decide, by native_decide⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The witness elements are not themselves squares. -/
example :
    (Nat.sqrt 3) ^ 2 ≠ 3 ∧ (Nat.sqrt 8) ^ 2 ≠ 8 ∧ (Nat.sqrt 192) ^ 2 ≠ 192 := by
  native_decide

end JSP000476
