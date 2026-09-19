/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000503 — Vertex subsets that are vertex sets of cycles

How many vertex subsets of a regular graph are exactly the vertex sets of
cycles?  Bounded instances for two 2-regular graphs on four vertices:

* in the cycle `C4`, exactly `1` of the 16 subsets is the vertex set of a
  cycle (the full set);
* in `K4` (which is 3-regular; the question's "high-degree" regime), exactly
  `5` are: the four triangles and the full set.

A subset is a *cycle vertex set* when the induced subgraph on it is a cycle
graph (connected 2-regular on ≥ 3 vertices).
-/

namespace Mega5.JSP000503

/-- Vertex subsets of `{0,1,2,3}` encoded by 4 bits. -/
abbrev pop4 (s : ℕ) : ℕ :=
  (if s.testBit 0 then 1 else 0) + (if s.testBit 1 then 1 else 0) +
  (if s.testBit 2 then 1 else 0) + (if s.testBit 3 then 1 else 0)

/-- `K4` adjacency. -/
abbrev k4 (i j : ℕ) : Bool := i ≠ j

/-- `C4` adjacency (cycle `0-1-2-3-0`). -/
abbrev c4 (i j : ℕ) : Bool := (i + 1) % 4 = j || (j + 1) % 4 = i

/-- Triangle on exactly the vertex set `s`. -/
abbrev triOn (adj : ℕ → ℕ → Bool) (s : ℕ) : Prop :=
  ∃ x y z : Fin 4, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    s.testBit x.val ∧ s.testBit y.val ∧ s.testBit z.val ∧
    (∀ v : Fin 4, v.val ≠ x.val ∧ v.val ≠ y.val ∧ v.val ≠ z.val → ¬ s.testBit v.val) ∧
    adj x.val y.val ∧ adj y.val z.val ∧ adj x.val z.val

/-- 4-cycle through exactly the vertex set `s` (all four vertices). -/
abbrev c4On (adj : ℕ → ℕ → Bool) (s : ℕ) : Prop :=
  (∃ x y z w : Fin 4, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧ w ≠ x ∧ x ≠ z ∧ y ≠ w ∧
    adj x.val y.val ∧ adj y.val z.val ∧ adj z.val w.val ∧ adj w.val x.val) ∧
  pop4 s = 4

/-- `s` is the vertex set of a cycle of `adj`. -/
abbrev CycleSet (adj : ℕ → ℕ → Bool) (s : ℕ) : Prop :=
  (pop4 s = 3 ∧ triOn adj s) ∨ (pop4 s = 4 ∧ c4On adj s)

/-- Number of vertex subsets that are vertex sets of cycles. -/
def countCycleSets (adj : ℕ → ℕ → Bool) : ℕ :=
  (List.range 16).filter (fun s => decide (CycleSet adj s)) |>.length

/-- In `C4` exactly one subset is a cycle vertex set. -/
theorem c4_count : countCycleSets c4 = 1 := by native_decide

/-- In `K4` exactly five subsets are cycle vertex sets. -/
theorem k4_count : countCycleSets k4 = 5 := by native_decide

end Mega5.JSP000503
