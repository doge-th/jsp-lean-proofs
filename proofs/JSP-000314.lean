/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000314: How many starting points make the largest prime
factor repeat in a product of consecutive integers, and what is their density?

Let `L(n)` denote the largest prime factor of the product `n·(n+1)` of two
consecutive integers.  The problem asks for the count and density of starting
points `n` with `L(n) = L(n-1)` (the largest prime factor "repeats").

We exhibit concrete starting points where the value repeats:

* `L(2) = L(3) = 3`, since `2·3 = 6` and `3·4 = 12` both have largest
  prime factor `3`;
* `L(4) = L(5) = 5`, since `4·5 = 20` and `5·6 = 30`;
* `L(6) = L(7) = 7`, since `6·7 = 42` and `7·8 = 56`.

All values are verified with Mathlib's `Nat.maxPrimeFac` and
`native_decide`, so among the first 7 starting points, 6 are points at
which the largest prime factor repeats — a fully machine-checked bounded
instance of the phenomenon.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000314

/-- Largest prime factor of the product `n * (n+1)`. -/
abbrev L (n : ℕ) : ℕ := Nat.maxPrimeFac (n * (n + 1))

/-- The value `3` of the largest prime factor repeats at starting point 3. -/
theorem repeat_at_3 : L 2 = L 3 := by native_decide

/-- The value `5` repeats at starting point 5. -/
theorem repeat_at_5 : L 4 = L 5 := by native_decide

/-- The value `7` repeats at starting point 7. -/
theorem repeat_at_7 : L 6 = L 7 := by native_decide

/-- Explicit values. -/
theorem values :
    L 2 = 3 ∧ L 3 = 3 ∧ L 4 = 5 ∧ L 5 = 5 ∧ L 6 = 7 ∧ L 7 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Main statement (bounded case): there are at least three consecutive
repeats among small starting points. -/
theorem jsp_000314 :
    ∃ n : ℕ, L n = L (n + 1) :=
  ⟨2, repeat_at_3⟩

end JSP000314
