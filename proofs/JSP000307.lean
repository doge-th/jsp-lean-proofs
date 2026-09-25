/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000307: Can three consecutive integers have strictly
decreasing largest prime factors?

We answer "yes" by exhibiting the triple (13, 14, 15), whose largest prime
factors are 13, 7, 5 respectively, and verifying the strict decrease with
`native_decide`.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000307

/-- The largest prime factor of a natural number `n` (using Mathlib's
canonical definition). For `n = 0` this is `0`, and for `n = 1` it is `1`;
for `n > 1` it is the greatest prime dividing `n`. -/
abbrev largestPrimeFactor (n : ℕ) : ℕ := Nat.maxPrimeFac n

/-- The conjectured statement: there exist three consecutive integers whose
largest prime factors are strictly decreasing.

This is the formal restatement of JSP-000307. We do NOT prove this in
full generality (it is an existential statement and would require a much
deeper search), but we provide concrete witnesses below. -/
theorem jsp_000307_statement : ∃ n : ℕ,
    largestPrimeFactor n > largestPrimeFactor (n + 1) ∧
    largestPrimeFactor (n + 1) > largestPrimeFactor (n + 2) := by
  -- Use `Exists.intro` to introduce the concrete witness `n = 13`.
  refine ⟨13, ?_⟩
  -- Reduce the goal to evaluating `maxPrimeFac` on 13, 14, 15, then check
  -- the resulting purely-arithmetic inequality.
  simp only [largestPrimeFactor]
  native_decide

/-- Concrete verification for the triple (13, 14, 15). -/
theorem triple_13_14_15 :
    largestPrimeFactor 13 > largestPrimeFactor 14 ∧
    largestPrimeFactor 14 > largestPrimeFactor 15 := by
  simp only [largestPrimeFactor]
  native_decide

/-- Explicit evaluation of `largestPrimeFactor` on the witness triple. -/
theorem triple_values :
    largestPrimeFactor 13 = 13 ∧
    largestPrimeFactor 14 = 7 ∧
    largestPrimeFactor 15 = 5 := by
  simp only [largestPrimeFactor]
  native_decide

end JSP000307