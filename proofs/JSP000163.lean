/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000163: How many vertices can a two-colored complete
graph have while avoiding a four-vertex clique in one color and a prescribed
large clique in the other (i.e. lower bounds for the Ramsey numbers
`R(4, k)`)?

We give the sharp small case `k = 3`: `R(4, 3) ≥ 9`.  The Möbius ladder on
8 vertices (the 8-cycle plus the four antipodal chords) is triangle-free
and has no independent set of four vertices.  Coloring its edges red and
all remaining edges blue therefore yields a 2-coloring of `K₈` with no red
triangle and no blue `K₄`, so `R(4, 3) > 8` (and by symmetry `R(3, 4) > 8`,
matching the exact value `R(3, 4) = 9`).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace JSP000163

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))


/-- Edge list of the Möbius ladder `M₈`: the 8-cycle `0-1-…-7-0` plus the
antipodal chords `04 15 26 37`. -/
def L8 : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0),
   (0, 4), (1, 5), (2, 6), (3, 7)]

/-- Red adjacency of the witness coloring of `K₈`. -/
def red8 (i j : Fin 8) : Bool := (i.val, j.val) ∈ L8 || (j.val, i.val) ∈ L8

/-- No red triangle. -/
theorem no_red_triangle :
    ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k →
      ¬ (red8 i j ∧ red8 j k ∧ red8 k i) := by
  native_decide

/-- No blue `K₄`: every four distinct vertices span a red edge. -/
theorem no_blue_K4 :
    ∀ q : Fin 4 → Fin 8, Function.Injective q →
      ∃ a b : Fin 4, a ≠ b ∧ red8 (q a) (q b) := by
  native_decide

/-- Combined: `R(4,3) > 8`, i.e. `R(4,3) ≥ 9`. -/
theorem R43_ge_9 :
    ∃ c : Fin 8 → Fin 8 → Bool,
      (∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k →
        ¬ (c i j ∧ c j k ∧ c k i)) ∧
      (∀ q : Fin 4 → Fin 8, Function.Injective q →
        ∃ a b : Fin 4, a ≠ b ∧ c (q a) (q b)) :=
  ⟨red8, no_red_triangle, no_blue_K4⟩

end JSP000163
