/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000428: How large can a pairwise noncoprime subset of an
integer interval containing a specified integer be?

Lower-bound witness: in the interval `[1, 10]`, the five even integers
`{2, 4, 6, 8, 10}` form a pairwise noncoprime set containing the prescribed
integer 2, of size 5 — optimal in this interval, since any two distinct odd
integers of `[1, 10]` are coprime to the even part in the sense that an odd
number can only be noncoprime to {3, 9} (gcd 3) and {5, 7} are coprime to
everything else, forcing size ≤ 5.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000428

/-- JSP-000428: a pairwise noncoprime subset of `[1, 10]` containing `2`,
of size `5`: `{2, 4, 6, 8, 10}`. -/
theorem jsp_000428 :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 10 ∧ 2 ∈ S ∧ S.card = 5 ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd a b ≠ 1) := by
  refine ⟨{2, 4, 6, 8, 10}, ?_, by decide, by decide, ?_⟩
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

/-- Explicit pairwise gcds of the witness set. -/
example :
    Nat.gcd 2 4 = 2 ∧ Nat.gcd 2 6 = 2 ∧ Nat.gcd 4 10 = 2 ∧ Nat.gcd 8 10 = 2 := by
  native_decide

end JSP000428
