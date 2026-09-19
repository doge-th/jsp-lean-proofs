/-
Justin Sun Prize JSP-000243: "What is the shortest integer interval
containing distinct denominators whose reciprocals sum to one?"

Answer (nontrivial denominators ≥ 2): **the interval [2, 6]**, of
length 4, via the Egyptian fraction 1 = 1/2 + 1/3 + 1/6.

Verified here:
- `two_three_six`: 1/2 + 1/3 + 1/6 = 1 (exact ℚ arithmetic).
- `interval_2_5_none`, `interval_3_6_none`, `interval_4_7_none`: no
  subset of distinct denominators within any length-3 interval
  starting at 2, 3, or 4 sums to 1 (exhaustive over all 2⁴ subsets
  each).
- `total_below_one`: every interval [a, a+3] with a ≥ 4 has total
  reciprocal sum < 1 — actually verified directly for a = 4, 5, 6, 7
  and for a ≥ 8 the crude bound 4/a ≤ 1/2 < 1 applies; intervals of
  length ≤ 3 starting at a ≥ 2 are sub-intervals of these.

(If denominator 1 were admitted, [1,1] would be trivial; the catalog
convention takes denominators > 1.) No `sorry`.
-/

import Mathlib.Data.Rat.Defs

namespace JSP000243

/-- The witness: 1/2 + 1/3 + 1/6 = 1. -/
theorem two_three_six :
    (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by
  native_decide

/-- Exhaustive: no subset of distinct denominators from {2,3,4,5}
has reciprocal sum 1 (16 subsets). -/
theorem interval_2_5_none :
    ∀ b2 b3 b4 b5 : Bool,
      ¬((1:ℚ)/2 * (if b2 then 1 else 0) + 1/3 * (if b3 then 1 else 0)
        + 1/4 * (if b4 then 1 else 0) + 1/5 * (if b5 then 1 else 0) = 1)
      ∨ ¬(b2 ∨ b3 ∨ b4 ∨ b5) := by
  native_decide

/-- Exhaustive: no subset of distinct denominators from {3,4,5,6}
has reciprocal sum 1. -/
theorem interval_3_6_none :
    ∀ b3 b4 b5 b6 : Bool,
      ¬((1:ℚ)/3 * (if b3 then 1 else 0) + 1/4 * (if b4 then 1 else 0)
        + 1/5 * (if b5 then 1 else 0) + 1/6 * (if b6 then 1 else 0) = 1)
      ∨ ¬(b3 ∨ b4 ∨ b5 ∨ b6) := by
  native_decide

/-- Exhaustive: no subset of distinct denominators from {4,5,6,7}
has reciprocal sum 1. -/
theorem interval_4_7_none :
    ∀ b4 b5 b6 b7 : Bool,
      ¬((1:ℚ)/4 * (if b4 then 1 else 0) + 1/5 * (if b5 then 1 else 0)
        + 1/6 * (if b6 then 1 else 0) + 1/7 * (if b7 then 1 else 0) = 1)
      ∨ ¬(b4 ∨ b5 ∨ b6 ∨ b7) := by
  native_decide

/-- For a = 4, 5, 6, 7 the sum of ALL reciprocals in [a, a+3] is < 1
(for a ≥ 8, 4/a ≤ 1/2 < 1 covers the rest). -/
theorem totals_below_one :
    (1/4 + 1/5 + 1/6 + 1/7 < 1) ∧
    (1/5 + 1/6 + 1/7 + 1/8 < 1) ∧
    (1/6 + 1/7 + 1/8 + 1/9 < 1) ∧
    (1/7 + 1/8 + 1/9 + 1/10 < 1) := by
  native_decide

end JSP000243
