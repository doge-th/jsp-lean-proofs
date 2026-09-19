/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000140: How many edge colors are necessary if every
four-vertex clique must contain at least five colors?

Bounded case: at `n = 5` the answer is exactly `5`.  Since every `K₄`
already spans six edges, at least five distinct colors are forced there by
hypothesis, and the exhibited coloring below uses only the five colors
`0, …, 4` while every 4-clique of `K₅` sees *all five* of them.  (This is
the first instance of the Erdős–Gyárfás `(p, q) = (4, 5)` local coloring
problem.)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace JSP000140

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))


/-- Association list giving the color of each edge `ij`, `i < j`, of `K₅`. -/
def L5 : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 1), ((0, 2), 0), ((0, 3), 2), ((0, 4), 3), ((1, 2), 3),
   ((1, 3), 0), ((1, 4), 4), ((2, 3), 4), ((2, 4), 2), ((3, 4), 1)]

/-- The 5-coloring of the edges of `K₅`. -/
def col5 (i j : Fin 5) : ℕ :=
  match List.lookup (i.val, j.val) L5 with
  | some v => v
  | none => match List.lookup (j.val, i.val) L5 with
    | some v => v
    | none => 0

/-- Only five colors are used altogether. -/
theorem palette_is_five :
    ∀ i j : Fin 5, col5 i j < 5 := by
  native_decide

/-- Every four-vertex clique of `K₅` contains all five colors, hence at
least five colors. -/
theorem every_K4_five_colors :
    ∀ q : Fin 4 → Fin 5, Function.Injective q →
      (List.range 5).all fun c =>
        [col5 (q 0) (q 1), col5 (q 0) (q 2), col5 (q 0) (q 3),
          col5 (q 1) (q 2), col5 (q 1) (q 3), col5 (q 2) (q 3)].any (· = c) := by
  native_decide

end JSP000140
