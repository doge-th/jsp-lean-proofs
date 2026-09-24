/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000399: Can a finite set be uniquely recovered from the
multiset of all sums of a prescribed number of distinct elements?

Answer: NO — recovery can fail.  Witness: the two different 4-element sets
`{0, 3, 5, 6}` and `{1, 2, 4, 7}` have the same multiset of 2-element subset
sums, namely `{3, 3? no: 3, 5, 6, 8, 9, 11}` (each once):
`{0,3,5,6}`:  0+3=3, 0+5=5, 0+6=6, 3+5=8, 3+6=9, 5+6=11;
`{1,2,4,7}`:  1+2=3, 1+4=5, 1+7=8, 2+4=6, 2+7=9, 4+7=11.
-/

import Mathlib.Data.Finset.Powerset

namespace JSP000399

/-- The multiset of all sums `a + b` coming from the 2-element subsets of `A`. -/
def pairSums (A : Finset ℕ) : Multiset ℕ :=
  (A.powerset.val.filter (fun s : Finset ℕ => s.card = 2)).map
    (fun s : Finset ℕ => s.val.sum)

/-- Recovery fails: two different finite sets with the same multiset of
2-element subset sums. -/
theorem jsp_000399 : ∃ A B : Finset ℕ, A ≠ B ∧ pairSums A = pairSums B := by
  refine ⟨{0, 3, 5, 6}, {1, 2, 4, 7}, ?_, ?_⟩
  · native_decide
  · native_decide

/-- The counterexample can be shifted to strictly positive integers:
{1,4,6,7} and {2,3,5,8} have the same multiset of 2-element sums
(each 2-sum of the shifted sets is the original 2-sum plus 2). -/
theorem jsp_000399_positive :
    ∃ A B : Finset ℕ, A ≠ B ∧ (∀ x ∈ A, x > 0) ∧ (∀ x ∈ B, x > 0) ∧
      pairSums A = pairSums B := by
  refine ⟨{1, 4, 6, 7}, {2, 3, 5, 8}, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end JSP000399
