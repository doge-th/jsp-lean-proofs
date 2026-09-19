/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000513 — Doubling list sizes and required color counts

Does `(a, b)`-list-multicolorability imply `(2a, 2b)`-list-multicolorability?
Bounded instance of the persistence property for the smallest graph with an
edge: `K2` is `(2,1)`-choosable and also `(4,2)`-choosable.

Here `(a, b)`-choosable means: for every assignment of `a`-element lists
there is a proper `b`-fold coloring, i.e. each vertex receives `b` distinct
colors from its list, adjacent vertices receiving disjoint sets.
Palettes: `{0,1,2}` for the `(2,1)` case (a 2-element list is encoded by its
missing color) and `{0,...,5}` for the `(4,2)` case (an `m`-element subset of
the 6-set is encoded by its complement pair).
-/

namespace Mega5.JSP000513

/-- List entry for vertex `i` in the `(2,1)` instance: the missing color. -/
abbrev Lom (L i : ℕ) : ℕ := (L / 3 ^ i) % 3

/-- Chosen color for vertex `i` in the `(2,1)` instance. -/
abbrev f21 (f i : ℕ) : ℕ := (f / 3 ^ i) % 3

/-- The fifteen pairs `{p, q} ⊆ {0..5}` by index. -/
def om2 (t : ℕ) : ℕ × ℕ :=
  if t = 0 then (0, 1) else if t = 1 then (0, 2) else if t = 2 then (0, 3) else
  if t = 3 then (0, 4) else if t = 4 then (0, 5) else if t = 5 then (1, 2) else
  if t = 6 then (1, 3) else if t = 7 then (1, 4) else if t = 8 then (1, 5) else
  if t = 9 then (2, 3) else if t = 10 then (2, 4) else if t = 11 then (2, 5) else
  if t = 12 then (3, 4) else if t = 13 then (3, 5) else (4, 5)

/-- `c` lies in the 4-element list encoded by `t` (complement pair `om2 t`). -/
def inL6 (t c : ℕ) : Bool := !(c == (om2 t).1) && !(c == (om2 t).2)

/-- `c` lies in the 2-element set encoded by `t` (the pair `om2 t`). -/
def inS2 (t c : ℕ) : Bool := c == (om2 t).1 || c == (om2 t).2

/-- `K2` is `(2,1)`-choosable over the palette `{0,1,2}`. -/
theorem K2_choosable :
    ∀ L : Fin 9, ∃ f : Fin 9,
      f21 f.val 0 ≠ f21 f.val 1 ∧
      f21 f.val 0 ≠ Lom L.val 0 ∧ f21 f.val 1 ≠ Lom L.val 1 := by
  native_decide

/-- The check that `S0, S1` is a proper `2`-fold choice for lists `L0, L1`:
    each chosen set is contained in the respective list and the two sets are
    disjoint (they both avoid each other's colors). -/
def goodChoice (L0 L1 S0 S1 : ℕ) : Bool :=
  ((List.range 6).all fun c => !(inS2 S0 c) || inL6 L0 c) &&
  ((List.range 6).all fun c => !(inS2 S1 c) || inL6 L1 c) &&
  ((List.range 6).all fun c => !(inS2 S0 c && inS2 S1 c))

/-- `K2` is `(4,2)`-choosable over the palette `{0,...,5}`: from any two
    4-element lists one can choose disjoint 2-element sets. -/
theorem K2_multicolor_double :
    ∀ L0 L1 : Fin 15, ∃ S0 S1 : Fin 15,
      goodChoice L0.val L1.val S0.val S1.val = true := by
  native_decide

end Mega5.JSP000513
