/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000357: How large can a subset of an integer interval be
if no two elements sum to a square?

Existence core settled here: in the interval `[1, 20]` a subset of size `10`
with no two distinct elements summing to a perfect square exists (the witness
below; `10` is in fact optimal for this interval, though optimality is not
proved here).  The general density results ([LOS83], [KLS02]) are not claimed.
-/

import Mathlib.Order.Interval.Finset.Nat

namespace JSP000357

/-- The witness set: ten integers in `[1, 20]`, no two distinct elements of
which add up to a perfect square. -/
def witness : Finset ℕ := {2, 4, 6, 8, 9, 11, 13, 15, 18, 20}

/-- A size-`10` subset of `[1, 20]` such that no two distinct elements sum to
a perfect square. -/
theorem jsp_000357 : ∃ s : Finset ℕ,
    s ⊆ Finset.Icc 1 20 ∧ s.card = 10 ∧
    ∀ x ∈ s, ∀ y ∈ s, x < y → Nat.sqrt (x + y) * Nat.sqrt (x + y) ≠ x + y := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro x hx
    simp [witness] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> exact Finset.mem_Icc.mpr (by omega)
  · native_decide
  · intro x hx y hy hxy
    simp [witness] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> first
        | native_decide
        | exact absurd hxy (by native_decide)

end JSP000357
