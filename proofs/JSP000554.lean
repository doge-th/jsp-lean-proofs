/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000554: Between consecutive primes, is there an integer
whose least prime factor is at least their gap?

Existence witness (answer: yes).  Between the consecutive primes 47 and 53
(gap 6) lies 49 = 7^2, whose least prime factor is 7 ≥ 6.  The primality
witnesses are checked with `native_decide`, as is the absence of primes
strictly between 47 and 53.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000554

/-- JSP-000554: consecutive primes 47, 53 with gap 6, and 49 = 7^2 strictly
between them has least prime factor 7 ≥ 6. -/
theorem jsp_000554 :
    ∃ p q m : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧
      (∀ k ∈ Finset.Icc (p + 1) (q - 1), ¬ Nat.Prime k) ∧
      p < m ∧ m < q ∧ q - p ≤ Nat.minFac m := by
  refine ⟨47, 53, 49, by native_decide, by native_decide, by native_decide,
    by decide, by decide, by native_decide⟩

/-- The composite numbers 48, 50, 51, 52 fill the gap: none is prime, and
49 = 7^2 has least prime factor 7. -/
example :
    ¬ Nat.Prime 48 ∧ ¬ Nat.Prime 50 ∧ ¬ Nat.Prime 51 ∧ ¬ Nat.Prime 52 ∧
      Nat.minFac 49 = 7 := by
  native_decide

end JSP000554
