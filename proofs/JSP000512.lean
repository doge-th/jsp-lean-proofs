/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000512 — List size guaranteeing proper list coloring of planar graphs

Thomassen's five-list theorem: every planar graph is colorable from lists of
size five.  Bounded instance: every planar graph on at most four vertices —
i.e. *every* graph on four vertices, since all such graphs are planar — is
colorable from arbitrary four-element lists drawn from a five-color palette.

Palette: colors `0..4`; a 4-element list omits exactly one color; a list
assignment is encoded in base 5 (the omitted color of vertex `i`).
-/

namespace Mega5.JSP000512

/-- Index of the edge `{i, j}` among the six pairs of `0,1,2,3`. -/
abbrev eidx4 (i j : ℕ) : ℕ :=
  if min i j = 0 then max i j - 1 else if min i j = 1 then max i j + 1 else 5

/-- Graph on vertices `0,1,2,3`, encoded by six bits. -/
abbrev adj (g i j : ℕ) : Bool := g.testBit (eidx4 i j)

/-- The color missing from the list of vertex `i`. -/
abbrev miss (L i : ℕ) : ℕ := (L / 5 ^ i) % 5

/-- The color chosen for vertex `i`. -/
abbrev fval (f i : ℕ) : ℕ := (f / 5 ^ i) % 5

/-- Every graph on four vertices is colorable from 4-element lists over a
    5-color palette (exhaustive over the 64 graphs, the 625 list assignments,
    and the 625 candidate colorings). -/
theorem four_choosable :
    ∀ g : Fin 64, ∀ L : Fin 625, ∃ f : Fin 625,
      (∀ i : Fin 4, fval f.val i.val ≠ miss L.val i.val) ∧
      (∀ i j : Fin 4, i ≠ j → adj g.val i.val j.val →
        fval f.val i.val ≠ fval f.val j.val) := by
  native_decide

end Mega5.JSP000512
