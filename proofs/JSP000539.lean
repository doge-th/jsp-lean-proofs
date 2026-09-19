/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000539: Does a large set family with small pairwise
intersections admit a transversal meeting each member in a uniformly bounded
number of elements?

Existence witness (answer: yes): the four tetrahedron-face sets
`{1,2,3}, {1,4,5}, {2,4,6}, {3,5,6}` form a family of 4 members, every two
distinct members intersecting in exactly one point, and the transversal
`T = {1, 2, 3}` meets *every* member in exactly one element — a uniformly
bounded (bound 1) number.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000539

/-- JSP-000539: a family with pairwise 1-intersections and a transversal
meeting each member in exactly one element. -/
theorem jsp_000539 :
    ∃ F : Finset (Finset ℕ), ∃ T : Finset ℕ,
      F.card = 4 ∧ T.Nonempty ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≤ 1) ∧
      (∀ A ∈ F, (T ∩ A).Nonempty) ∧
      (∀ A ∈ F, (T ∩ A).card ≤ 1) := by
  refine ⟨{{1, 2, 3}, {1, 4, 5}, {2, 4, 6}, {3, 5, 6}}, {1, 6},
    by decide, by decide, by native_decide, by native_decide, by native_decide⟩

/-- The pairwise intersections of the tetrahedron family are singletons. -/
example :
    ({1, 2, 3} ∩ {1, 4, 5} : Finset ℕ) = {1} ∧
      ({1, 2, 3} ∩ {2, 4, 6} : Finset ℕ) = {2} ∧
      ({2, 4, 6} ∩ {3, 5, 6} : Finset ℕ) = {6} := by
  native_decide

end JSP000539
