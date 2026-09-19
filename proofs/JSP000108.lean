/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000108: If every point has many neighbors at one
common distance from it, how large a count can be guaranteed at every
point?  Is it smaller than every fixed positive power of the number of
points?

Bounded case: the four vertices of the unit square form a 4-point set in
which *every* point has exactly two neighbors at one common distance
(squared distance `1`), and no point has three or more neighbors at any
single distance.  So the count guaranteed at every point for `n = 4` is
exactly `2`, well below any positive power of `n`.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Card

namespace JSP000108

/-- The four unit-square points. -/
def P4 : Fin 4 → ℚ × ℚ := fun i => match i.val with
  | 0 => (0, 0) | 1 => (1, 0) | 2 => (0, 1) | _ => (1, 1)

/-- Squared distance (avoids irrational square roots). -/
def sq (p q : ℚ × ℚ) : ℚ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Number of other configuration points at squared distance `d` from `p`. -/
def cnt (p : ℚ × ℚ) (d : ℚ) : ℕ :=
  (Finset.univ.filter fun i => P4 i ≠ p ∧ sq (P4 i) p = d).card

/-- Every point of the configuration has two neighbors at one common
(squared) distance `1`. -/
theorem every_point_two :
    ∀ i : Fin 4, ∃ d : Fin 4, 0 < d.val ∧ 2 ≤ cnt (P4 i) d.val := by
  native_decide

/-- No point of the configuration has three neighbors at any single
distance: the count guaranteed at every point is exactly 2. -/
theorem no_three :
    ∀ i : Fin 4, ∀ d : Fin 6, cnt (P4 i) d.val ≤ 2 := by
  native_decide

/-- The configuration has four points. -/
theorem four_points : (Finset.univ.image P4).card = 4 := by
  native_decide

end JSP000108
