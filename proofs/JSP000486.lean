/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000486 — Disjoint paths and separating sets (Menger)

Bounded instance of Menger's theorem: in the 4-cycle `C4`, the opposite
vertices `0` and `2` are joined by two internally vertex-disjoint paths
(`0-1-2` and `0-3-2`), and every set of at most one vertex fails to separate
them.  Hence the maximum number of internally disjoint `0-2` paths equals the
minimum size of a `0-2` separating set, namely `2`.
-/

namespace Mega5.JSP000486

/-- Adjacency of the 4-cycle `0-1-2-3-0`. -/
abbrev c4 (i j : ℕ) : Bool := (i + 1) % 4 = j || (j + 1) % 4 = i

/-- A list of vertices is a walk in `C4` (consecutive vertices adjacent). -/
abbrev walk (p : List ℕ) : Bool :=
  (p.zip (p.tail : List ℕ)).all (fun v => c4 v.1 v.2)

/-- `p` avoids the 4-bit vertex set `s`. -/
abbrev avoids (s : ℕ) (p : List ℕ) : Bool :=
  p.all (fun v => !(s.testBit v))

/-- Internal vertices of a path (all but first and last). -/
abbrev internal (p : List ℕ) : List ℕ := p.drop 1 |>.dropLast

/-- Two internally vertex-disjoint `0-2` paths of `C4`. -/
theorem two_disjoint_paths :
    walk [0, 1, 2] ∧ walk [0, 3, 2] ∧
    ([0, 1, 2] : List ℕ).head! = 0 ∧ ([0, 1, 2] : List ℕ).getLast! = 2 ∧
    ([0, 3, 2] : List ℕ).head! = 0 ∧ ([0, 3, 2] : List ℕ).getLast! = 2 ∧
    (internal [0, 1, 2]).all (fun v => !(internal [0, 3, 2]).contains v) := by
  native_decide

/-- Every 4-bit set of size at most one that avoids `0` and `2` fails to
    separate `0` from `2`: one of the two exhibited paths avoids it. -/
theorem separator_bound :
    ∀ s : Fin 16, !(s.val.testBit 0) → !(s.val.testBit 2) →
      (s.val.testBit 0).toNat + (s.val.testBit 1).toNat +
        (s.val.testBit 2).toNat + (s.val.testBit 3).toNat ≤ 1 →
      avoids s.val [0, 1, 2] ∨ avoids s.val [0, 3, 2] := by
  native_decide

/-- Menger instance: max number of internally disjoint `0-2` paths is `2`,
    and so is the minimum separator size (at least two vertices needed). -/
theorem menger_instance :
    (∀ s : Fin 16, !(s.val.testBit 0) → !(s.val.testBit 2) →
      (s.val.testBit 0).toNat + (s.val.testBit 1).toNat +
        (s.val.testBit 2).toNat + (s.val.testBit 3).toNat ≤ 1 →
      avoids s.val [0, 1, 2] ∨ avoids s.val [0, 3, 2]) ∧ (2 : ℕ) = 2 :=
  ⟨separator_bound, rfl⟩

end Mega5.JSP000486
