/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000216: How much larger than a zero-density integer
set can its sumset with itself be?

Answer (bounded instances): far larger — the set of powers of two is a
zero-density set whose sumset with itself has essentially quadratic size,
because all sums `2^i + 2^j` (i ≤ j) are distinct.  Concretely:

* for `A = {1, 2, 4, 8, 16}` (5 elements) the restricted sumset
  `A + A = {2,3,4,5,6,8,9,10,12,16,17,18,20,24,32}` has 15 = 3·|A| elements;
* for `A = {1, 2, …, 256}` (9 powers of two) the sumset has
  45 = 5·|A| elements.

As |A| grows the ratio |A+A| / |A| = (n+1)/2 is unbounded while the
density of A tends to zero, so no bound of the form |A+A| ≤ C·|A| can
hold for zero-density sets.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry

/-- JSP-000216: powers of two with 5 and 9 elements: the sumset is 3 resp.
5 times as large as the set. -/
theorem jsp_000216 :
    (∃ A : Finset ℕ, A.card = 5 ∧
      ((A ×ˢ A).image (fun p => p.1 + p.2)).card = 3 * A.card) ∧
    (∃ A : Finset ℕ, A.card = 9 ∧
      ((A ×ˢ A).image (fun p => p.1 + p.2)).card = 5 * A.card) :=
  ⟨⟨{1, 2, 4, 8, 16}, by native_decide, by native_decide⟩,
   ⟨{1, 2, 4, 8, 16, 32, 64, 128, 256}, by native_decide, by native_decide⟩⟩
