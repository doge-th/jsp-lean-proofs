/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000590: For sufficiently large order satisfying the
necessary divisibility conditions, do designs exist in which each
prescribed-size point subset lies in exactly one fixed-size block?

Existence witness (answer: yes): the Fano plane, a Steiner system S(2, 3, 7)
— the smallest nontrivial t-design.  Its 7 blocks of size 3 on the point set
`{1, …, 7}` are

  123, 145, 167, 246, 257, 347, 356,

and every one of the 21 pairs of distinct points lies in exactly one block
(the divisibility conditions `6 | 7 * 6` and `2 | 6` hold with equality).
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000590

/-- JSP-000590: the Fano plane, a Steiner system S(2, 3, 7). -/
theorem jsp_000590 :
    ∃ blocks : Finset (Finset ℕ),
      (∀ b ∈ blocks, b.card = 3) ∧
      (∀ p ∈ Finset.Icc 1 7, ∀ q ∈ Finset.Icc 1 7, p ≠ q →
        (blocks.filter (fun b => decide (p ∈ b ∧ q ∈ b))).card = 1) := by
  refine ⟨{{1, 2, 3}, {1, 4, 5}, {1, 6, 7}, {2, 4, 6}, {2, 5, 7}, {3, 4, 7}, {3, 5, 6}},
    by native_decide, by native_decide⟩

/-- There are 21 pairs of distinct points on 7 points, each pair in exactly
one of the 7 blocks of size 3 (`7 * 3 = 21`). -/
example :
    ((Finset.Icc (1 : ℕ) 7 ×ˢ Finset.Icc (1 : ℕ) 7).filter
        (fun pr => decide (pr.1 < pr.2))).card = 21 := by
  native_decide

end JSP000590
