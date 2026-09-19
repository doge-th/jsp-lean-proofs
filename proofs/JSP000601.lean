/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000601: How many distinct line-multiplicity counting
sequences can planar point sets determine?

Lower-bound witness (answer: at least 3 already for 4 points).  For a point
set `P` we compute, for every unordered pair of points, the number of points
of `P` on the line they span; a line carrying `k` points contributes
`k (k-1) / 2` copies of `k`, so this multiset determines the classical
line-multiplicity counting sequence `(n_2, n_3, …)`.  Three 4-point
configurations yield three distinct sequences:

  general position    : {2,2,2,2,2,2}   (six 2-point lines),
  exactly 3 collinear : {3,3,3,2,2,2}   (one 3-point + three 2-point lines),
  all 4 collinear     : {4,4,4,4,4,4}   (one 4-point line).
-/

import Mathlib.Data.Nat.MaxPrimeFac
import Mathlib.Data.Finset.Prod

namespace JSP000601

/-- Strict order on lattice points selecting each unordered pair once. -/
def ltP (a b : ℤ × ℤ) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

/-- Collinearity of three lattice points: the cross product vanishes. -/
def collin (a b c : ℤ × ℤ) : Bool :=
  (c.1 - a.1) * (b.2 - a.2) == (c.2 - a.2) * (b.1 - a.1)

/-- The line-multiplicity multiset of a finite point set. -/
def lineSeq (P : Finset (ℤ × ℤ)) : Multiset ℕ :=
  ((P ×ˢ P).filter fun pr => ltP pr.1 pr.2).val.map
    fun pr => (P.filter fun r => collin pr.1 pr.2 r).card

/-- JSP-000601: three 4-point planar configurations with pairwise distinct
line-multiplicity counting sequences. -/
theorem jsp_000601 :
    ∃ A B C : Finset (ℤ × ℤ),
      A.card = 4 ∧ B.card = 4 ∧ C.card = 4 ∧
      lineSeq A ≠ lineSeq B ∧ lineSeq B ≠ lineSeq C ∧ lineSeq A ≠ lineSeq C := by
  refine ⟨{(0, 0), (1, 0), (0, 1), (2, 3)},
    {(0, 0), (1, 0), (2, 0), (0, 1)},
    {(0, 0), (1, 0), (2, 0), (3, 0)},
    by decide, by decide, by decide,
    by native_decide, by native_decide, by native_decide⟩

/-- The three sequences: `{2×6}`, `{3×3, 2×3}`, `{4×6}`. -/
example :
    lineSeq ({(0, 0), (1, 0), (0, 1), (2, 3)} : Finset (ℤ × ℤ)) = {2, 2, 2, 2, 2, 2} ∧
      lineSeq ({(0, 0), (1, 0), (2, 0), (0, 1)} : Finset (ℤ × ℤ)) = {3, 3, 3, 2, 2, 2} ∧
      lineSeq ({(0, 0), (1, 0), (2, 0), (3, 0)} : Finset (ℤ × ℤ)) = {4, 4, 4, 4, 4, 4} := by
  native_decide

end JSP000601
