/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000468 — Spanning hypercubes in random graphs

The theorem states that for suitable parameters `G(n, p)` contains a spanning
hypercube asymptotically almost surely.  Bounded instance: we exhibit a
spanning hypercube `Q3` inside the densest random graph `G(8, 1)`, i.e. the
complete graph on 8 vertices, by identifying the vertex set of `Q3` with
`Fin 8 = {0,1}^3` (edges at Hamming distance one).

We verify that this subgraph
* is a genuine subgraph of the complete graph (its edges are edges of `K8`),
* has exactly `12` edges and is `3`-regular (so it is the cube `Q3`),
* is bipartite (parity coloring), hence spanning on all 8 vertices.
-/

namespace Mega5.JSP000468

/-- Hamming weight of a 3-bit word. -/
abbrev pop3 (x : ℕ) : ℕ :=
  (if x.testBit 0 then 1 else 0) +
  (if x.testBit 1 then 1 else 0) +
  (if x.testBit 2 then 1 else 0)

/-- Adjacency of the hypercube `Q3` on the vertex set `Fin 8 = {0,1}^3`. -/
abbrev cube (x y : ℕ) : Bool := pop3 (Nat.xor x y) = 1

/-- `Q3` is a subgraph of the complete graph `K8`. -/
theorem subgraph_of_complete :
    ∀ x y : Fin 8, cube x.val y.val → x ≠ y := by
  native_decide

/-- `Q3` has exactly 12 edges. -/
theorem edge_count :
    (((List.range 8).flatMap
      (fun x => (List.range 8).filter (fun y => x < y && cube x y))).length) = 12 := by
  native_decide

/-- `Q3` is 3-regular. -/
theorem three_regular :
    ∀ x : Fin 8,
      ((List.range 8).filter (fun y => y ≠ x.val && cube x.val y)).length = 3 := by
  native_decide

/-- `Q3` is bipartite: adjacent vertices have Hamming weights of opposite
    parity. -/
theorem bipartite :
    ∀ x y : Fin 8, cube x.val y.val → pop3 x.val % 2 ≠ pop3 y.val % 2 := by
  native_decide

end Mega5.JSP000468
