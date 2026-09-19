/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000464 — Extremal edges when excluding an odd cycle and an adjacent even cycle

Bounded instance: the maximum number of edges of a graph on `4` vertices
containing neither a triangle (odd cycle `C3`) nor a `C4` (the adjacent even
cycle) is `3`.

* Upper bound: every graph on 4 vertices with at least 4 edges contains a
  triangle or a 4-cycle — checked by exhaustive enumeration of all 64 graphs.
* Lower bound: the 3-edge star `K_{1,3}` excludes both.
-/

namespace Mega5.JSP000464

/-- Index of the edge `{i, j}` among the six pairs of `0,1,2,3`. -/
abbrev eidx4 (i j : ℕ) : ℕ :=
  if min i j = 0 then max i j - 1 else if min i j = 1 then max i j + 1 else 5

/-- Graph on vertices `0,1,2,3`, encoded by six bits. -/
abbrev adj (g i j : ℕ) : Bool := g.testBit (eidx4 i j)

/-- A triangle `C3`. -/
abbrev Tri (g : ℕ) : Prop :=
  ∃ x y z : Fin 4, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    adj g x.val y.val ∧ adj g y.val z.val ∧ adj g x.val z.val

/-- A 4-cycle `C4`. -/
abbrev C4 (g : ℕ) : Prop :=
  ∃ x y z w : Fin 4, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ x ∧ x ≠ z ∧ y ≠ w ∧
    adj g x.val y.val ∧ adj g y.val z.val ∧ adj g z.val w.val ∧ adj g w.val x.val

/-- Number of edges of a 4-vertex graph. -/
abbrev m4 (g : ℕ) : ℕ :=
  (List.range 6).filter (fun i => g.testBit i) |>.length

/-- Upper bound: a triangle-free, `C4`-free graph on 4 vertices has at most
    3 edges (exhaustive over all 64 graphs). -/
theorem ex_upper : ∀ g : Fin 64, m4 g.val ≤ 3 ∨ Tri g.val ∨ C4 g.val := by
  native_decide

/-- Lower bound: the star `K_{1,3}` has 3 edges, no triangle, no 4-cycle. -/
theorem star_extremal : m4 7 = 3 ∧ ¬ Tri 7 ∧ ¬ C4 7 := by native_decide

/-- The extremal number for `{C3, C4}` on four vertices is exactly `3`. -/
theorem ex_of_four :
    (∀ g : Fin 64, ¬ Tri g.val → ¬ C4 g.val → m4 g.val ≤ 3) ∧
    (m4 7 = 3 ∧ ¬ Tri 7 ∧ ¬ C4 7) := by
  refine ⟨?_, star_extremal⟩
  intro g ht hc
  cases ex_upper g with
  | inl h => exact h
  | inr h =>
    cases h with
    | inl h => exact absurd h ht
    | inr h => exact absurd h hc

end Mega5.JSP000464
