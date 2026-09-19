/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000440 — Two-color Ramsey number of a tree with bipartition ratio 1 : 2

The smallest tree whose bipartition sizes have ratio one to two is the star
`K_{1,2}` (the path on three vertices).  As a bounded instance of the general
question we determine its two-color Ramsey number exactly: `R(K_{1,2}) = 3`.

* Upper bound: every red/blue coloring of the edges of `K3` contains a
  monochromatic copy of `K_{1,2}`.
* Lower bound: some coloring of the single edge of `K2` avoids one.
-/

namespace Mega5.JSP000440

/-- Index of the edge `{i, j}` among the three edges of `K3`. -/
abbrev eidx (i j : ℕ) : ℕ := if min i j = 0 then max i j - 1 else 2

/-- A red/blue coloring of the edges of `K3`, encoded by three bits. -/
abbrev col (k i j : ℕ) : Bool := k.testBit (eidx i j)

/-- `k` contains a monochromatic copy of the star `K_{1,2}` (center `x`). -/
abbrev MonoStar (k : ℕ) : Prop :=
  ∃ x y z : Fin 3, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    col k x.val y.val = col k x.val z.val

/-- Upper bound: every coloring of `K3` contains a monochromatic `K_{1,2}`. -/
theorem exists_mono : ∀ k : Fin 8, MonoStar k.val := by
  native_decide

/-- A coloring of the edges of `K2` (one bit). -/
abbrev col2 (k : ℕ) : Bool := k.testBit 0

/-- A monochromatic copy of the star `K_{1,2}` inside `K2`. -/
abbrev MonoStar2 (k : ℕ) : Prop :=
  ∃ x y z : Fin 2, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    col2 k = col2 k

/-- Lower bound: every coloring of `K2` contains no monochromatic `K_{1,2}`
    (there are not three distinct vertices). -/
theorem lower_bound : ∀ k : Fin 2, ¬ MonoStar2 k.val := by
  native_decide

/-- The two-color Ramsey number of the 1:2 tree `K_{1,2}` is exactly `3`. -/
theorem ramsey_eq_three :
    (∀ k : Fin 8, MonoStar k.val) ∧ (∀ k : Fin 2, ¬ MonoStar2 k.val) :=
  ⟨exists_mono, lower_bound⟩

end Mega5.JSP000440
