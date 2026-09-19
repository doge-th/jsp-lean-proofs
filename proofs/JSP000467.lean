/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000467 — Minimum degree forcing vertex-disjoint 4-cycles

The general theorem (Enomoto–Wang type): minimum degree `2k` forces `k`
vertex-disjoint cycles.  Bounded instance with `k = 1` and four vertices:
every graph on `4` vertices of minimum degree at least `2` contains a
*spanning* 4-cycle (one 4-cycle covering all four vertices).

The result is proved by exhaustive enumeration of all 64 graphs, and shown
sharp: minimum degree `1` does not suffice.
-/

namespace Mega5.JSP000467

/-- Index of the edge `{i, j}` among the six pairs of `0,1,2,3`. -/
abbrev eidx4 (i j : ℕ) : ℕ :=
  if min i j = 0 then max i j - 1 else if min i j = 1 then max i j + 1 else 5

/-- Graph on vertices `0,1,2,3`, encoded by six bits. -/
abbrev adj (g i j : ℕ) : Bool := g.testBit (eidx4 i j)

/-- Degree of vertex `i`. -/
abbrev deg (g i : ℕ) : ℕ :=
  (List.range 4).filter (fun j => j ≠ i && adj g i j) |>.length

/-- Minimum degree at least two. -/
abbrev minDeg2 (g : ℕ) : Prop := ∀ i : Fin 4, 2 ≤ deg g i.val

/-- A spanning 4-cycle (four distinct vertices in a cyclic edge pattern). -/
abbrev SpanC4 (g : ℕ) : Prop :=
  ∃ x y z w : Fin 4, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ x ∧ x ≠ z ∧ y ≠ w ∧
    adj g x.val y.val ∧ adj g y.val z.val ∧ adj g z.val w.val ∧ adj g w.val x.val

/-- Main instance: minimum degree `≥ 2` on four vertices forces a spanning
    4-cycle (exhaustive over all 64 graphs). -/
theorem min_degree_forces : ∀ g : Fin 64, SpanC4 g.val ∨ ¬ minDeg2 g.val := by
  native_decide

theorem four_cycle_theorem : ∀ g : Fin 64, minDeg2 g.val → SpanC4 g.val := by
  intro g h
  cases min_degree_forces g with
  | inl h' => exact h'
  | inr h' => exact absurd h h'

/-- Sharpness: the triangle `0-1-2` with pendant edge `0-3` has a vertex of
    degree `1` and no spanning 4-cycle. -/
theorem sharpness :
    deg 15 3 = 1 ∧ deg 15 0 = 3 ∧ ¬ SpanC4 15 := by
  native_decide

end Mega5.JSP000467
