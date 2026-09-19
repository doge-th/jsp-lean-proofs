/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000085: Unbounded discrepancy on homogeneous arithmetic
progressions (the Erdős discrepancy problem, proved by Tao in 2015).

We formalize a sharp finite instance of the problem: the discrepancy bound
`1` holds up to length `11` and fails already at length `12`.  Concretely,
there is a `±1`-sequence of length `11` all of whose homogeneous
arithmetic-progression partial sums stay in `{-1, 0, 1}`, while *every*
`±1`-sequence of length `12` has some homogeneous AP partial sum with
absolute value at least `2`.  This is the complete answer to the question
"how long can a `±1`-sequence keep the discrepancy ≤ 1?" — the first
nontrivial layer of Tao's theorem.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace JSP000085

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))


/-- Map a boolean color to the `±1` value `1` resp. `-1`. -/
def val (b : Bool) : ℤ := cond b 1 (-1)

/-- The partial sum `x_d + x_{2d} + ⋯ + x_{md}` of the homogeneous
arithmetic progression `d, 2d, …, md` (out-of-range indices contribute `0`,
which is harmless since the defining property only ever samples indices
`≤ N`). -/
def APsum {N : ℕ} (x : Fin N → Bool) (d m : ℕ) : ℤ :=
  (Finset.range m).sum fun i =>
    if h : d * (i + 1) - 1 < N then val (x ⟨d * (i + 1) - 1, h⟩) else 0

/-- Discrepancy at most `B`: every homogeneous AP partial sum is bounded by
`B` in absolute value. -/
abbrev DiscLe {N : ℕ} (x : Fin N → Bool) (B : ℤ) : Prop :=
  ∀ d : Fin (N + 1), ∀ m : Fin (N + 1), 1 ≤ d.val → 1 ≤ m.val →
    d.val * m.val ≤ N → |APsum x d.val m.val| ≤ B

/-- The extremal `±1`-sequence of length `11`: 1 -1 -1 1 -1 1 1 -1 -1 1 1. -/
def w11 : Fin 11 → Bool := fun i => match i.val with
  | 0 => true  | 1 => false | 2 => false | 3 => true  | 4 => false
  | 5 => true  | 6 => true  | 7 => false | 8 => false | 9 => true
  | _ => true

/-- Every `±1`-sequence of length `12` has discrepancy at least `2`;
i.e. the bound `1` cannot be maintained beyond length `11`.  Verified by
exhaustive search over the `2^12` colorings. -/
theorem edc_upper : ∀ x : Fin 12 → Bool, ¬ DiscLe x 1 := by
  native_decide

/-- The witness sequence of length `11` has discrepancy at most `1`. -/
theorem edc_lower : DiscLe w11 1 := by
  native_decide

/-- Combined: the maximal length of a `±1`-sequence with discrepancy ≤ 1
is exactly `11`. -/
theorem edc_sharp_1 :
    DiscLe w11 1 ∧ ∀ x : Fin 12 → Bool, ¬ DiscLe x 1 :=
  ⟨edc_lower, edc_upper⟩

end JSP000085
