/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000471 — Bipartite subgraphs of triangle-free graphs

How many edges can always be retained in a bipartite subgraph?  Every graph
admits a cut retaining at least half its edges.  Bounded instance for
triangle-free graphs on four vertices: every triangle-free graph `g` has a
cut with `2 * (crossing edges) ≥ (edges of g)`.

Also recorded: the 3-edge star `K_{1,3}` is triangle-free and its maximum cut
retains *all* its edges.
-/

namespace Mega5.JSP000471

/-- Index of the edge `{i, j}` among the six pairs of `0,1,2,3`. -/
abbrev eidx4 (i j : ℕ) : ℕ :=
  if min i j = 0 then max i j - 1 else if min i j = 1 then max i j + 1 else 5

/-- Graph on vertices `0,1,2,3`, encoded by six bits. -/
abbrev adj (g i j : ℕ) : Bool := g.testBit (eidx4 i j)

/-- A triangle. -/
abbrev Tri (g : ℕ) : Prop :=
  ∃ x y z : Fin 4, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    adj g x.val y.val ∧ adj g y.val z.val ∧ adj g x.val z.val

/-- Number of edges of a 4-vertex graph. -/
abbrev m4 (g : ℕ) : ℕ :=
  (List.range 6).filter (fun i => g.testBit i) |>.length

/-- Number of edges crossing the cut given by the 4-bit set `s`. -/
abbrev cross (g s : ℕ) : ℕ :=
  ((List.range 4).flatMap
    (fun i => (List.range 4).filter
      (fun j => i < j && adj g i j && (s.testBit i != s.testBit j)))).length

/-- Every triangle-free 4-vertex graph has a cut retaining at least half its
    edges (exhaustive over all 64 graphs and all 16 cuts). -/
theorem half_retained :
    ∀ g : Fin 64, ¬ Tri g.val →
      ∃ s : Fin 16, 2 * cross g.val s.val ≥ m4 g.val := by
  native_decide

/-- The star `K_{1,3}` is triangle-free and the cut isolating its center
    retains all three edges. -/
theorem star_all_retained :
    (¬ Tri 7) ∧ (m4 7 = 3) ∧ (cross 7 1 = 3) ∧ (2 * cross 7 1 ≥ m4 7) := by
  native_decide

end Mega5.JSP000471
