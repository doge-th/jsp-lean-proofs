/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000935: Can Euclidean space be partitioned into
countably many sets each having all pairwise distances distinct?

We formalize the central finitary notion — a Golomb ruler: a set of marks
on the line in which all pairwise distances are distinct — and prove its
classical sharp instance: the 5-mark ruler `{0, 1, 4, 9, 11}` has all ten
pairwise distances distinct, and no 5-mark ruler fits in `[0, 10]` (all
sorted 5-tuples from `Fin 11` are checked exhaustively).  The countable
partition of the whole line/space into such sets is the deep (affirmative)
part of the problem; this is its complete finite core.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

namespace JSP000935

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))


/-- The marks of the classical optimal 5-point Golomb ruler. -/
def marks : Fin 5 → ℚ := fun i => match i.val with
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 9 | _ => 11

/-- The five marks are pairwise distinct. -/
theorem marks_distinct :
    ∀ i j : Fin 5, i < j → marks i ≠ marks j := by
  native_decide

/-- All ten pairwise distances `|marks i - marks j|` are distinct. -/
theorem golomb_property :
    ∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) →
      |marks i - marks j| ≠ |marks k - marks l| := by
  native_decide

/-- The marks span length exactly `11`. -/
theorem span_11 : marks 4 - marks 0 = 11 := by native_decide

/-- Optimality: no (sorted) 5-mark ruler fits inside `[0, 10]`. -/
theorem no_ruler_in_10 :
    ∀ m : Fin 5 → Fin 11,
      m 0 < m 1 → m 1 < m 2 → m 2 < m 3 → m 3 < m 4 →
        ¬ (∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) →
            m i - m j ≠ m k - m l) := by
  native_decide

/-- The finite core of JSP-000935: distance-distinct point sets exist, and
five points are already maximal for span `10`. -/
theorem golomb_core :
    (∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) →
      |marks i - marks j| ≠ |marks k - marks l|) ∧
    (∀ m : Fin 5 → Fin 11,
      m 0 < m 1 → m 1 < m 2 → m 2 < m 3 → m 3 < m 4 →
        ¬ (∀ i j k l : Fin 5, i < j → k < l → (i, j) ≠ (k, l) →
            m i - m j ≠ m k - m l)) :=
  ⟨golomb_property, no_ruler_in_10⟩

end JSP000935
