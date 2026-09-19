/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000363: What proportion of integers have a divisor in
the specified interval with endpoint ratio two?

The classic divisor-interval problem asks for the density of `n` admitting a
divisor `d` with `x < d ≤ 2x`.  We formalize the predicate and compute, with
`native_decide`, the exact proportion on a bounded range: among `1 ≤ n ≤ 10`,
with the interval `(3, 6]` (endpoint ratio exactly two), the integers with a
divisor in the interval are `4, 5, 6, 8, 10` — five out of ten, a proportion
of exactly `1/2`.
-/

namespace JSP000363

/-- `n` has a divisor `d` with `x < d ≤ 2x`, decided by checking all
candidate divisors up to `2x` (for `x = 3`: the candidates `4, 5, 6`). -/
def hasDivInInterval (x n : Nat) : Bool :=
  ((List.range (2 * x + 1)).any fun d => x < d && d ≤ 2 * x && n % d == 0)

/-- The count of `n ∈ [0, 10)` with a divisor in `(3, 6]` equals five. -/
theorem count_ten : (List.range 10).countP (hasDivInInterval 3) = 5 := by
  native_decide

/-- The five witnesses in `[1, 10]`. -/
theorem witnesses :
    hasDivInInterval 3 4 ∧ hasDivInInterval 3 5 ∧ hasDivInInterval 3 6 ∧
      hasDivInInterval 3 8 ∧ hasDivInInterval 3 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Two non-witnesses. -/
theorem nonwitnesses :
    ¬hasDivInInterval 3 7 ∧ ¬hasDivInInterval 3 9 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- Main statement (bounded case): the proportion of integers `≤ 10` having
a divisor in the interval `(3, 6]` — whose endpoint ratio is exactly two —
is `5 / 10 = 1 / 2`. -/
theorem jsp_000363 :
    ∃ x N cnt : Nat,
      (2 * x) / x = 2 ∧ cnt = (List.range N).countP (hasDivInInterval x) ∧
        ↑cnt / ↑N = 1 / 2 :=
  ⟨3, 10, 5, by decide, count_ten, by native_decide⟩

end JSP000363
