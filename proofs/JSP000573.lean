/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000573: How large can a set family be if a prescribed
pairwise intersection size is forbidden?

Lower-bound witness: forbid intersection size exactly 1 on the ground set
`{1, 2, 3, 4}`.  The 6-member family

  ∅, {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}, {1,2,3,4}

has every two distinct members intersecting in 0, 2 or 3 elements — never 1.
(Six is optimal here: adding any singleton or 2-set creates a forbidden
intersection with one of the 3-sets.)
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000573

/-- JSP-000573: a 6-member family on 4 points with no pairwise intersection
of size exactly 1. -/
theorem jsp_000573 :
    ∃ F : Finset (Finset ℕ), F.card = 6 ∧
      (∀ A ∈ F, A ⊆ {1, 2, 3, 4}) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ 1) := by
  refine ⟨{∅, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {1, 2, 3, 4}},
    by decide, by native_decide, by native_decide⟩

/-- The intersection sizes realised inside the family: 0, 2 and 3. -/
example :
    ({1, 2, 3} ∩ {1, 2, 4} : Finset ℕ).card = 2 ∧
      ({1, 2, 3} ∩ {2, 3, 4} : Finset ℕ).card = 2 ∧
      ({1, 2, 3} ∩ {1, 2, 3, 4} : Finset ℕ).card = 3 ∧
      ((∅ : Finset ℕ) ∩ {1, 2, 3} : Finset ℕ).card = 0 := by
  native_decide

end JSP000573
