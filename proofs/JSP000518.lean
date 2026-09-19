/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000518 — Large induced subgraphs with many distinct degrees

If a graph has neither large cliques nor large independent sets, must a large
induced subgraph have many distinct vertex degrees?

Bounded instance: the 5-cycle `C5` (no triangle, no independent triple) has
an induced subgraph on `4` of its `5` vertices — a path `P4` — whose degrees
take exactly two distinct values, `1` and `2`.
-/

namespace Mega5.JSP000518

/-- Adjacency of the 5-cycle. -/
abbrev c5 (i j : ℕ) : Bool := (i + 1) % 5 = j || (j + 1) % 5 = i

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

/-- Size of a 5-bit subset. -/
abbrev pop5 (s : ℕ) : ℕ :=
  (if s.testBit 0 then 1 else 0) + (if s.testBit 1 then 1 else 0) +
  (if s.testBit 2 then 1 else 0) + (if s.testBit 3 then 1 else 0) +
  (if s.testBit 4 then 1 else 0)

/-- Degree of `i` in the subgraph induced by the 5-bit set `s`. -/
abbrev degIn (s i : ℕ) : ℕ :=
  (List.range 5).filter (fun j => j ≠ i && s.testBit j && c5 i j) |>.length

/-- Number of distinct degrees within an induced subgraph. -/
def dedup : List ℕ → List ℕ
  | [] => []
  | a :: t => if (dedup t).contains a then dedup t else a :: dedup t

abbrev distinctDegrees (s : ℕ) : ℕ :=
  (dedup ((List.range 5).filter (s.testBit ·) |>.map (degIn s))).length

/-- The subset `0b01111` (vertices `0,1,2,3`, which induce `P4`) is large
    (four of five vertices) and has exactly two distinct degrees. -/
theorem four_subset_two_degrees :
    pop5 0b01111 = 4 ∧
    distinctDegrees 0b01111 = 2 ∧
    degIn 0b01111 0 = 1 ∧ degIn 0b01111 1 = 2 ∧
    degIn 0b01111 2 = 2 ∧ degIn 0b01111 3 = 1 := by
  native_decide

/-- Every 4-vertex induced subgraph of `C5` (a `P4`) has two distinct
    degrees, and the degrees are `1` and `2`. -/
theorem all_four_subsets :
    ∀ s : Fin 32, pop5 s.val = 4 →
      distinctDegrees s.val = 2 := by
  native_decide

end Mega5.JSP000518
