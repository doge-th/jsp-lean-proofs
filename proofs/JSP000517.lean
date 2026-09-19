/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000517 — Induced subgraphs with distinct (vertex, edge) count pairs

If a graph has no clique or independent set larger than logarithmic size, must
it have many induced subgraphs with distinct pairs of vertex and edge counts?

Bounded instance: the 5-cycle `C5` has no triangle and no independent triple
(`ω, α = 2 ≤ log2 5`), and its 32 vertex subsets realize `8` distinct
(vertex-count, edge-count) pairs — realized by exhaustive enumeration.
-/

namespace Mega5.JSP000517

/-- Adjacency of the 5-cycle. -/
abbrev c5 (i j : ℕ) : Bool := (i + 1) % 5 = j || (j + 1) % 5 = i

/-- Size of a 5-bit subset. -/
abbrev pop5 (s : ℕ) : ℕ :=
  (if s.testBit 0 then 1 else 0) + (if s.testBit 1 then 1 else 0) +
  (if s.testBit 2 then 1 else 0) + (if s.testBit 3 then 1 else 0) +
  (if s.testBit 4 then 1 else 0)

/-- Number of induced edges of the subgraph on the 5-bit subset `s`. -/
abbrev inducedEdges (s : ℕ) : ℕ :=
  ((List.range 5).flatMap
    (fun i => (List.range 5).filter
      (fun j => i < j && s.testBit i && s.testBit j && c5 i j))).length

/-- No triangle. -/
theorem no_triangle :
    ∀ x y z : Fin 5, x ≠ y → y ≠ z → x ≠ z →
      ¬ (c5 x.val y.val ∧ c5 y.val z.val ∧ c5 x.val z.val) := by
  native_decide

/-- No independent set of size three. -/
theorem no_independent_triple :
    ∀ x y z : Fin 5, x ≠ y → y ≠ z → x ≠ z →
      c5 x.val y.val ∨ c5 x.val z.val ∨ c5 y.val z.val := by
  native_decide

/-- Deduplicate a list of number pairs. -/
def dedup2 : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | a :: t => if (dedup2 t).contains a then dedup2 t else a :: dedup2 t

/-- The distinct (vertex-count, edge-count) pairs over all 32 subsets. -/
def pairData : List (ℕ × ℕ) :=
  (List.range 32).map (fun s => (pop5 s, inducedEdges s))

/-- `C5` realizes exactly eight distinct (vertex, edge) count pairs. -/
theorem eight_pairs : (dedup2 pairData).length = 8 := by
  native_decide

/-- The eight realized pairs, explicitly. -/
theorem pairs_explicit :
    dedup2 pairData = [(0, 0), (1, 0), (2, 0), (2, 1), (3, 1), (3, 2), (4, 3), (5, 5)] := by
  native_decide

end Mega5.JSP000517
