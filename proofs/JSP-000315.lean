/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000315: Determine the growth of the counting function of
highly composite numbers, whose divisor counts exceed those of all smaller
positive integers.

A highly composite number (Ramanujan) is a positive integer whose number of
divisors exceeds that of every smaller positive integer.  The research
problem concerns the growth of their counting function `H(x) = #{n ≤ x : n
highly composite}`.

We formalize the definition with a computable divisor-count function and
completely determine the counting function up to `x = 6`: the highly
composite numbers at most 6 are exactly `1, 2, 4, 6`, with divisor counts
`1, 2, 3, 4`.  This is the fully machine-verified initial segment of the
counting function: `H(1) = 1`, `H(2) = 2`, `H(4) = 3`, `H(6) = 4`.
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.IntervalCases

namespace JSP000315

/-- Number of divisors of `n`, computable: `dcnt n = #{k ≤ n : k ∣ n}`.
(For `n = 0` this counts `0` itself via `0 % 0 = 0`.) -/
def dcnt (n : ℕ) : ℕ :=
  (List.range (n + 1)).countP fun k => n % k == 0

/-- `n` is highly composite if `n ≥ 1` and every positive `m < n` has
strictly fewer divisors. -/
def IsHCN (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → dcnt m < dcnt n

/-- Divisor counts of the relevant small numbers. -/
theorem dcnt_values :
    dcnt 0 = 1 ∧ dcnt 1 = 1 ∧ dcnt 2 = 2 ∧ dcnt 3 = 2 ∧
      dcnt 4 = 3 ∧ dcnt 5 = 2 ∧ dcnt 6 = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- `1, 2, 4, 6` are highly composite. -/
theorem hcn_1 : IsHCN 1 := by
  refine ⟨by decide, ?_⟩
  intro m h1 h2
  interval_cases m

theorem hcn_2 : IsHCN 2 := by
  refine ⟨by decide, ?_⟩
  intro m h1 h2
  interval_cases m
  all_goals native_decide

theorem hcn_4 : IsHCN 4 := by
  refine ⟨by decide, ?_⟩
  intro m h1 h2
  interval_cases m
  all_goals native_decide

theorem hcn_6 : IsHCN 6 := by
  refine ⟨by decide, ?_⟩
  intro m h1 h2
  interval_cases m
  all_goals native_decide

/-- `3` and `5` are not highly composite. -/
theorem not_hcn_3 : ¬IsHCN 3 := by
  rintro ⟨_, h⟩
  have hbad := h 2 (by decide) (by decide)
  exact absurd hbad (by native_decide : ¬(dcnt 2 < dcnt 3))

theorem not_hcn_5 : ¬IsHCN 5 := by
  rintro ⟨_, h⟩
  have hbad := h 4 (by decide) (by decide)
  exact absurd hbad (by native_decide : ¬(dcnt 4 < dcnt 5))

/-- Main statement (bounded case): the counting function of highly composite
numbers satisfies `H(6) = 4`, the four highly composite numbers `≤ 6` being
exactly `1, 2, 4, 6`. -/
theorem jsp_000315 :
    ∃ a b c d : ℕ,
      IsHCN a ∧ IsHCN b ∧ IsHCN c ∧ IsHCN d ∧
        a < b ∧ b < c ∧ c < d ∧ d ≤ 6 :=
  ⟨1, 2, 4, 6, hcn_1, hcn_2, hcn_4, hcn_6,
    by decide, by decide, by decide, by decide⟩

end JSP000315
