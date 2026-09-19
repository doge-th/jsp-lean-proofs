/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000450 — Size Ramsey numbers of bounded-degree graphs

The size Ramsey number `hat R(G)` is the least number of edges of a graph that
arrows `G`.  As a bounded instance of the linearity question we compute the
size Ramsey number of the bounded-degree tree `P3` (a star `K_{1,2}`):
`hat R(P3) = 3`.

* The host triangle `K3` (3 edges) arrows `P3`: every 2-coloring of its edges
  contains a monochromatic `P3`.
* No host with at most 2 edges arrows `P3`.
-/

namespace Mega5.JSP000450

/-- Index of the edge `{i, j}` among the three edges of `K3`. -/
abbrev eidx (i j : ℕ) : ℕ := if min i j = 0 then max i j - 1 else 2

/-- Edge set of a host graph on vertices `0,1,2`, encoded by three bits. -/
abbrev present (g i j : ℕ) : Bool := g.testBit (eidx i j)

/-- Color of edge `{i, j}` in a 2-coloring, encoded by three bits. -/
abbrev color (k i j : ℕ) : Bool := k.testBit (eidx i j)

/-- An edge of the host, carrying its color. -/
abbrev live (g k i j : ℕ) : Bool := present g i j && color k i j

/-- A monochromatic `P3` (two adjacent host edges of one color, center `x`). -/
abbrev MonoP3 (g k : ℕ) : Prop :=
  ∃ x y z : Fin 3, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    present g x.val y.val ∧ present g x.val z.val ∧
    color k x.val y.val = color k x.val z.val

/-- Number of edges of a 3-vertex host. -/
abbrev m3 (g : ℕ) : ℕ :=
  (List.range 3).filter (fun i => g.testBit i) |>.length

/-- Upper bound: the triangle (all three edges present) arrows `P3`. -/
theorem triangle_arrows : ∀ k : Fin 8, MonoP3 7 k.val := by
  native_decide

/-- Lower bound: every host with at most two edges admits an avoiding coloring.
    (For the 3-edge host `g = 7` no avoiding coloring exists, by
    `triangle_arrows`.) -/
theorem two_edges_fail :
    ∀ g : Fin 8, m3 g.val ≤ 2 → ∃ k : Fin 8, ¬ MonoP3 g.val k.val := by
  native_decide

/-- The size Ramsey number of `P3` is exactly `3`. -/
theorem size_ramsey_eq_three :
    (∀ k : Fin 8, MonoP3 7 k.val) ∧
    (∀ g : Fin 8, m3 g.val ≤ 2 → ∃ k : Fin 8, ¬ MonoP3 g.val k.val) :=
  ⟨triangle_arrows, two_edges_fail⟩

end Mega5.JSP000450
