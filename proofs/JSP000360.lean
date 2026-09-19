/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000360: How large can an integer set be if every pairwise
least common multiple is bounded by a prescribed value?

Existence core settled here: for the prescribed value `24` there is a 7-element
set (inside `[1, 24]`) whose pairwise lcms are all `≤ 24`, namely the proper
divisors of `24`.  The exact extremal function studied in [Ch72b], [Ch98] is
not claimed.
-/

import Mathlib.Order.Interval.Finset.Nat

namespace JSP000360

/-- The witness set: the proper divisors of `24`. -/
def witness : Finset ℕ := {1, 2, 3, 4, 6, 8, 12}

/-- A 7-element subset of `[1, 24]` in which every pairwise least common
multiple is at most `24`. -/
theorem jsp_000360 : ∃ s : Finset ℕ,
    s ⊆ Finset.Icc 1 24 ∧ s.card = 7 ∧
    ∀ x ∈ s, ∀ y ∈ s, Nat.lcm x y ≤ 24 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro x hx
    simp [witness] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> exact Finset.mem_Icc.mpr (by omega)
  · native_decide
  · intro x hx y hy
    simp [witness] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> native_decide

end JSP000360
