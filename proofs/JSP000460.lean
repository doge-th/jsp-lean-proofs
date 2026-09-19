/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000460 — Ramsey number of a prescribed cycle against any graph

Bounded instance of the bound `R(C_n, G) ≤ 2 e(G) + 1`: for the 3-cycle
against the single-edge graph `K2` we show the exact value
`R(C3, K2) = 3 = 2 * 1 + 1`.

* Upper bound: every red/blue coloring of the edges of `K3` contains a red
  triangle or a blue edge (the whole of `K2`).
* Lower bound: the coloring of the lone edge of `K2` red contains neither.
-/

namespace Mega5.JSP000460

/-- Index of the edge `{i, j}` among the three edges of `K3`. -/
abbrev eidx (i j : ℕ) : ℕ := if min i j = 0 then max i j - 1 else 2

/-- Red/blue coloring of the edges of `K3`, encoded by three bits
    (`true` = red). -/
abbrev col (k i j : ℕ) : Bool := k.testBit (eidx i j)

/-- A red triangle. -/
abbrev RedTri (k : ℕ) : Prop :=
  ∃ x y z : Fin 3, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    col k x.val y.val ∧ col k y.val z.val ∧ col k x.val z.val

/-- A blue edge (a blue copy of `K2`). -/
abbrev BlueEdge (k : ℕ) : Prop :=
  ∃ x y : Fin 3, x ≠ y ∧ ¬ col k x.val y.val

/-- Upper bound: every coloring of `K3` has a red triangle or a blue edge. -/
theorem upper : ∀ k : Fin 8, RedTri k.val ∨ BlueEdge k.val := by
  native_decide

/-- A coloring of the single edge of `K2` (`true` = red). -/
abbrev col2 (k : ℕ) : Bool := k.testBit 0

/-- A red triangle inside `K2` (impossible: too few vertices). -/
abbrev RedTri2 (_k : ℕ) : Prop :=
  ∃ x y z : Fin 2, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ True

/-- A blue edge inside `K2`. -/
abbrev BlueEdge2 (k : ℕ) : Prop :=
  ∃ x y : Fin 2, x ≠ y ∧ ¬ col2 k

/-- Lower bound: coloring the single edge of `K2` red avoids both. -/
theorem lower : ¬ RedTri2 1 ∧ ¬ BlueEdge2 1 := by native_decide

/-- `R(C3, K2) = 3 = 2 * e(K2) + 1`. -/
theorem ramsey_value :
    (∀ k : Fin 8, RedTri k.val ∨ BlueEdge k.val) ∧
    (¬ RedTri2 1 ∧ ¬ BlueEdge2 1) ∧
    ((3 : ℕ) = 2 * 1 + 1) :=
  ⟨upper, lower, rfl⟩

end Mega5.JSP000460
