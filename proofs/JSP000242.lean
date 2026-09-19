/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000242: Large smallest denominator in representations of one

In a representation of 1 as a prescribed number of positive unit fractions,
how large can the smallest denominator be?  Witness: 1 admits a
representation as a sum of **11 distinct** unit fractions whose smallest
denominator is **6**:

  1 = 1/6 + 1/7 + 1/8 + 1/9 + 1/10 + 1/12
        + 1/14 + 1/15 + 1/18 + 1/24 + 1/28,

verified exactly by `native_decide`.  (For comparison, with fewer terms the
smallest denominator is forced smaller: the 3-term representations of 1,
`1/2 + 1/3 + 1/6`, have smallest denominator 2, and a 5-term representation
exists with smallest denominator 3, cf. JSP000248's `rep_twenty`.)
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs

namespace JSP000242

/-- Reciprocal sum of a list of denominators, exactly in `ℚ`. -/
def qsum (L : List ℕ) : ℚ := L.foldr (fun d s => (d : ℚ)⁻¹ + s) 0

/-- All denominators at least 6, pairwise distinct. -/
def SmallDistint (L : List ℕ) (m : ℕ) : Prop :=
  (∀ d ∈ L, m ≤ d) ∧ L.Pairwise (· ≠ ·)

/-- The main witness: 1 as 11 distinct unit fractions, all with denominator
at least 6. -/
theorem rep_min_six :
    SmallDistint [6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28] 6 ∧
      qsum [6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28] = 1 :=
  ⟨⟨by decide, by decide⟩, by native_decide⟩

/-- The 11-term representation has smallest denominator exactly 6 (the
denominator 6 itself occurs). -/
theorem min_is_six :
    qsum [6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28] = 1 ∧
      6 ∈ [6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28] ∧
      List.Pairwise (· ≠ ·) [6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28] :=
  ⟨by native_decide, by decide, by decide⟩

/-- A sharper 10-term representation with smallest denominator 5. -/
theorem rep_min_five :
    SmallDistint [5, 6, 7, 8, 9, 10, 12, 40, 42, 45] 5 ∧
      qsum [5, 6, 7, 8, 9, 10, 12, 40, 42, 45] = 1 :=
  ⟨⟨by decide, by decide⟩, by native_decide⟩

/-- Existence form: for `k = 10` and `k = 11` prescribed terms, the smallest
denominator can be forced up to 5 and 6 respectively. -/
theorem exists_large_min :
    (∃ L : List ℕ, L.length = 10 ∧ SmallDistint L 5 ∧ qsum L = 1) ∧
    (∃ L : List ℕ, L.length = 11 ∧ SmallDistint L 6 ∧ qsum L = 1) := by
  refine ⟨⟨[5, 6, 7, 8, 9, 10, 12, 40, 42, 45], by decide, ⟨by decide, by decide⟩,
    by native_decide⟩,
    ⟨[6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28], by decide, ⟨by decide, by decide⟩,
    by native_decide⟩⟩

end JSP000242
