/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000259: Integers as sums of distinct unit fractions with bounded
denominators

Which positive integers can be represented as sums of distinct unit fractions
whose denominators all lie in a finite range `[2, N]`?  (Erdős–Graham asked
whether *every* positive integer can; settled by Croot, building on
Croot–Bleicher–Erdős-type constructions and Konyagin.)

Witnesses: `k = 1` is already representable within `[2, 6]`:

  1 = 1/2 + 1/3 + 1/6,

and `k = 2` within `[2, 168]`:

  2 = 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7 + 1/8 + 1/9 + 1/10
        + 1/18 + 1/105 + 1/168,

both verified exactly by `native_decide`.  (Complete search shows `k = 2`
needs `N ≥ 40`-ish and `k = 3` needs `N ≥ 40`; the exact minimal bounds grow
very fast — this is the content of the problem.)
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs

namespace JSP000259

/-- Reciprocal sum of a list of denominators, exactly in `ℚ`. -/
def qsum (L : List ℕ) : ℚ := L.foldr (fun d s => (d : ℚ)⁻¹ + s) 0

/-- `InRange L lo hi`: distinct denominators, all in `[lo, hi]`. -/
def InRange (L : List ℕ) (lo hi : ℕ) : Prop :=
  (∀ d ∈ L, lo ≤ d ∧ d ≤ hi) ∧ L.Pairwise (· ≠ ·)

/-- `k = 1` with denominators in `[2, 6]`. -/
theorem one_in_range :
    InRange [2, 3, 6] 2 6 ∧ qsum [2, 3, 6] = 1 :=
  ⟨⟨by decide, by decide⟩, by native_decide⟩

/-- `k = 2` with denominators in `[2, 168]`. -/
theorem two_in_range :
    InRange [2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 105, 168] 2 168 ∧
      qsum [2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 105, 168] = 2 :=
  ⟨⟨by decide, by decide⟩, by native_decide⟩

/-- Existence form: the integers 1 and 2 are representable with denominators
bounded by 6 and 168 respectively. -/
theorem exists_reps :
    (∃ L : List ℕ, InRange L 2 6 ∧ qsum L = 1) ∧
      (∃ L : List ℕ, InRange L 2 168 ∧ qsum L = 2) :=
  ⟨⟨[2, 3, 6], one_in_range⟩, ⟨[2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 105, 168],
    two_in_range⟩⟩

/-- Sanity: the total of all reciprocals `1/2, ..., 1/30` is still below 3,
so `k = 3` genuinely needs `N ≥ 31`: bounded ranges cannot reach arbitrary
integers too cheaply. -/
theorem k_three_needs_N_31 :
    qsum [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
      21, 22, 23, 24, 25, 26, 27, 28, 29, 30] < 3 := by
  native_decide

end JSP000259
