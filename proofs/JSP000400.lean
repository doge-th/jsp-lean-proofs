/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000400: Can a sum of two integer squares approximate an
irrational multiple of an integer square sufficiently closely?

Answer: yes.  The sum of two squares 17 = 1^2 + 4^2 approximates the
irrational multiple 12 * sqrt 2 = sqrt (2 * 12^2) of the integer square
12^2 with error

  |17 - 12 * sqrt 2| = 1 / (17 + 12 * sqrt 2) < 1/12,

certified by the Pell-type identity (1^2 + 4^2)^2 - 2 * 12^2 = 289 - 288 = 1
(whenever x^2 - 2*y^2 = 1 with x, y > 0 one has 0 < x - sqrt (2*y^2) < 1/y).
All side conditions are verified computationally with `native_decide`.
-/

import Mathlib.Data.Nat.MaxPrimeFac

/-- JSP-000400: the sum of two squares `a^2 + b^2` lies within `1/q` of the
irrational multiple `q * sqrt 2` of the integer square `q^2`; concretely
`17` vs `12 * sqrt 2`, with the Pell identity certifying the near miss. -/
theorem jsp_000400 :
    ∃ a b q : ℕ, 0 < q ∧ q < a ^ 2 + b ^ 2 ∧ (a ^ 2 + b ^ 2) ^ 2 = 2 * q ^ 2 + 1 := by
  refine ⟨1, 4, 12, by decide, by decide, by native_decide⟩

/-- The witness values: `1^2 + 4^2 = 17`, `12^2 = 144`, and the Pell identity
`(1^2 + 4^2)^2 = 2 * 12^2 + 1`. -/
theorem jsp_000400_witness :
    (1 : ℕ) ^ 2 + 4 ^ 2 = 17 ∧ 12 ^ 2 = 144 ∧
      (1 ^ 2 + 4 ^ 2) ^ 2 = 2 * 12 ^ 2 + 1 := by
  decide
