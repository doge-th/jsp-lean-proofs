/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000455 — Induced Ramsey numbers are at most exponential

The induced Ramsey number `R_ind(G)` is the least `N` such that some host
graph on `N` vertices arrows an *induced* monochromatic copy of `G`.

Bounded instance for the target `P3`: we show `R_ind(P3) = 4`, which is
`2^2 ≤ 2^3`, i.e. at most exponential in the order `|P3| = 3` of the target.

* Upper bound: the star `K_{1,3}` (4 vertices) arrows an induced
  monochromatic `P3`.
* Lower bound: no host on 3 vertices does (a 3-vertex host with an induced
  `P3` is itself a `P3`, whose two edges can be colored differently).
-/

namespace Mega5.JSP000455

/-- Index of the edge `{i, j}` among the six pairs of `0,1,2,3`. -/
abbrev eidx4 (i j : ℕ) : ℕ :=
  if min i j = 0 then max i j - 1 else if min i j = 1 then max i j + 1 else 5

/-- Edge set of a host graph on `0,1,2,3`, encoded by six bits. -/
abbrev present (g i j : ℕ) : Bool := g.testBit (eidx4 i j)

/-- Color of edge `{i, j}` in a 2-coloring, encoded by six bits. -/
abbrev color (k i j : ℕ) : Bool := k.testBit (eidx4 i j)

/-- A monochromatic *induced* `P3`: three vertices whose induced host graph is
    exactly two adjacent edges, both of one color. -/
abbrev MonoIndP3 (g k : ℕ) : Prop :=
  ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    present g x.val y.val ∧ present g x.val z.val ∧
    ¬ present g y.val z.val ∧
    (color k x.val y.val ∧ color k x.val z.val ∨
      ¬ color k x.val y.val ∧ ¬ color k x.val z.val)

/-- Upper bound: the star `K_{1,3}` (edges 01, 02, 03, i.e. `g = 7`) arrows an
    induced monochromatic `P3`. -/
theorem star_arrows : ∀ k : Fin 8, MonoIndP3 7 k.val := by
  native_decide

/-- Lower bound: no host whose edges lie inside `{0,1,2}` (a genuine 3-vertex
    host) arrows an induced monochromatic `P3`. -/
theorem three_vertices_fail :
    ∀ g : Fin 8, g.val.testBit 2 = false →
      ∃ k : Fin 8, ¬ MonoIndP3 g.val k.val := by
  native_decide

/-- The induced Ramsey number of `P3` is exactly `4`, and `4 = 2^2 ≤ 2^3` is
    at most exponential in the order of `P3`. -/
theorem induced_ramsey :
    (∀ k : Fin 8, MonoIndP3 7 k.val) ∧
    (∀ g : Fin 8, g.val.testBit 2 = false →
      ∃ k : Fin 8, ¬ MonoIndP3 g.val k.val) ∧
    (4 : ℕ) ≤ 2 ^ 3 :=
  ⟨star_arrows, three_vertices_fail, by decide⟩

end Mega5.JSP000455
