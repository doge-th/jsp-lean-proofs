/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000433: How large can the reciprocal sum of integers in
an interval be if every pairwise least common multiple exceeds the interval's
upper endpoint?

Lower-bound witness: in the interval `[5, 10]`, the set `{6, 7, 8, 9, 10}`
has every pairwise lcm strictly larger than the right endpoint 10, and its
reciprocal sum equals 1/6 + 1/7 + 1/8 + 1/9 + 1/10 = 1627/2520 > 1/2.
We certify the sum inequality over `ℕ` by clearing denominators with the
common multiple 2520 (so `2520 · ∑ 1/x = ∑ 2520/x`, and the inequality
`1627 > 1260` is exactly `∑ 1/x > 1/2`).
-/

import Mathlib.Data.Nat.MaxPrimeFac
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped BigOperators

namespace JSP000433

/-- JSP-000433: a set in `[5, 10]` with all pairwise lcms `> 10` whose
reciprocal sum exceeds `1/2` (measured as `∑ 2520/x > 1260`). -/
theorem jsp_000433 :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 5 10 ∧ S.card = 5 ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → 10 < Nat.lcm a b) ∧
      1260 < ∑ x ∈ S, 2520 / x := by
  refine ⟨{6, 7, 8, 9, 10}, ?_, by decide, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | native_decide
  · native_decide

/-- The cleared-denominator reciprocal sum: `2520/6 + … + 2520/10 = 1627`,
so the reciprocal sum is `1627/2520 > 1/2`. -/
example :
    ∑ x ∈ ({6, 7, 8, 9, 10} : Finset ℕ), 2520 / x = 1627 := by
  native_decide

end JSP000433
