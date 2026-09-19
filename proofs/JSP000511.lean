/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000511 — List coloring of planar bipartite graphs

Thomassen's theorem: every planar bipartite graph is colorable from arbitrary
lists of three colors per vertex.  Bounded instance on the smallest
interesting planar bipartite graph: the 4-cycle `C4` is colorable from any
assignment of two-element lists drawn from a 3-color palette — and, in
contrast, the odd cycle `C5` is *not* colorable from two-element lists.

Palette: colors `0, 1, 2`; the three two-element lists are
`0 ↦ {0,1}, 1 ↦ {0,2}, 2 ↦ {1,2}`.
-/

namespace Mega5.JSP000511

/-- The three 2-element lists, by index. -/
abbrev subL (t : ℕ) : ℕ × ℕ :=
  if t = 0 then (0, 1) else if t = 1 then (0, 2) else (1, 2)

/-- List assignment to the vertices `0..3` (a vertex is a `Fin 4`),
    encoded in base 3. -/
abbrev Lval (L i : ℕ) : ℕ := (L / 3 ^ i) % 3

/-- Color chosen for vertex `i`, encoded in base 3. -/
abbrev fval (f i : ℕ) : ℕ := (f / 3 ^ i) % 3

/-- Membership of a color in a 2-element list. -/
abbrev memL (t c : ℕ) : Prop := c = (subL t).1 ∨ c = (subL t).2

/-- `C4` is colorable from arbitrary 2-element lists of a 3-color palette. -/
theorem C4_choosable :
    ∀ L : Fin 81, ∃ f : Fin 81, ∀ i : Fin 4,
      memL (Lval L.val i.val) (fval f.val i.val) ∧
      fval f.val i.val ≠ fval f.val ((i.val + 1) % 4) := by
  native_decide

/-- `C5` is not colorable from two-element lists: the constant list
    `{0, 1}` admits no proper coloring. -/
theorem C5_not_choosable :
    ∀ f : Fin 243, ∃ i : Fin 5,
      fval f.val i.val = fval f.val ((i.val + 1) % 5) ∨
      ¬ (fval f.val i.val = 0 ∨ fval f.val i.val = 1) := by
  native_decide

end Mega5.JSP000511
