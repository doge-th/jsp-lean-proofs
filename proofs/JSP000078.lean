/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000078: How does the number of distinct odd cycle
lengths constrain a graph's chromatic number?

Bounded case: the 5-cycle `C₅` has exactly one odd cycle length (namely
`5`: it has no triangles, and its own 5-cycle is odd), yet its chromatic
number is `3`, not `2`.  We verify both facts exhaustively: no 3-clique
exists, the pentagon itself is a cycle, a proper 3-coloring is exhibited,
and every 2-coloring (all `2^5 = 32` are checked) fails.
-/

import Mathlib.Data.Fintype.Basic

namespace JSP000078

/-- Adjacency of the 5-cycle on vertices `Fin 5`. -/
def c5adj (i j : Fin 5) : Bool :=
  (i.val + 1) % 5 = j.val || (j.val + 1) % 5 = i.val

/-- No odd cycle of length 3 (no triangle). -/
theorem no_odd_cycle_3 :
    ∀ i j k : Fin 5, c5adj i j → c5adj j k → c5adj k i → False := by
  native_decide

/-- An odd cycle of length 5 exists: the pentagon itself. -/
theorem odd_cycle_5 :
    c5adj 0 1 ∧ c5adj 1 2 ∧ c5adj 2 3 ∧ c5adj 3 4 ∧ c5adj 4 0 ∧
      (0 : Fin 5) ≠ 1 ∧ (1 : Fin 5) ≠ 2 ∧ (2 : Fin 5) ≠ 3 ∧ (3 : Fin 5) ≠ 4 ∧
      (4 : Fin 5) ≠ 0 := by
  decide

/-- `C₅` is properly 3-colorable (witness coloring `0 1 2 1 2`). -/
def col3 : Fin 5 → Fin 3 := fun i => match i.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1 | _ => 2

theorem three_colorable :
    ∀ i j : Fin 5, c5adj i j → col3 i ≠ col3 j := by
  native_decide

/-- `C₅` is not 2-colorable: every assignment of two colors to the five
vertices identifies the colors of adjacent vertices somewhere. -/
theorem not_two_colorable :
    ∀ c : Fin 5 → Fin 2, ∃ i j : Fin 5, c5adj i j ∧ c i = c j := by
  native_decide

/-- Combined: `C₅` has exactly one odd cycle length and chromatic
number exactly 3. -/
theorem one_odd_length_chi_three :
    (∀ i j k : Fin 5, c5adj i j → c5adj j k → c5adj k i → False) ∧
    (∃ c : Fin 5 → Fin 3, ∀ i j : Fin 5, c5adj i j → c i ≠ c j) ∧
    (∀ c : Fin 5 → Fin 2, ∃ i j : Fin 5, c5adj i j ∧ c i = c j) :=
  ⟨no_odd_cycle_3, ⟨col3, three_colorable⟩, not_two_colorable⟩

end JSP000078
