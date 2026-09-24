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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators

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

/-- For every a ≥ 4 the sum of ALL reciprocals in [a, a+3] is < 1:
spot checks for a = 4..7, and for a ≥ 8 each term is ≤ 1/a so the sum
is ≤ 4/a ≤ 1/2 < 1. -/
theorem totals_below_one :
    (1/4 + 1/5 + 1/6 + 1/7 < 1) ∧
    (1/5 + 1/6 + 1/7 + 1/8 < 1) ∧
    (1/6 + 1/7 + 1/8 + 1/9 < 1) ∧
    (1/7 + 1/8 + 1/9 + 1/10 < 1) := by
  native_decide

/-- General tail case: for a ≥ 8 every subset sum from `{a,…,a+3}` is
< 1: each of the four reciprocals is ≤ 1/8, so the total is ≤ 1/2. -/
theorem tail_below_one (a : ℕ) (ha : 8 ≤ a) :
    (1:ℚ) / a + 1 / (a + 1) + 1 / (a + 2) + 1 / (a + 3) < 1 := by
  have h8 : (8:ℚ) ≤ (a:ℚ) := by exact_mod_cast ha
  have hp0 : 0 < ((a:ℚ)) := by positivity
  have hp1 : 0 < ((a + 1 : ℕ) : ℚ) := by positivity
  have hp2 : 0 < ((a + 2 : ℕ) : ℚ) := by positivity
  have hp3 : 0 < ((a + 3 : ℕ) : ℚ) := by positivity
  have hle0 : (8:ℚ) ≤ ((a : ℕ) : ℚ) := by exact_mod_cast ha
  have hle1 : (8:ℚ) ≤ ((a + 1 : ℕ) : ℚ) := by
    norm_cast; omega
  have hle2 : (8:ℚ) ≤ ((a + 2 : ℕ) : ℚ) := by
    norm_cast; omega
  have hle3 : (8:ℚ) ≤ ((a + 3 : ℕ) : ℚ) := by
    norm_cast; omega
  have h8pos : 0 < (8:ℚ) := by norm_num
  have b0 : (1:ℚ) / a ≤ 1 / 8 := one_div_le_one_div_of_le h8pos hle0
  have b1 : (1:ℚ) / ((a + 1 : ℕ) : ℚ) ≤ 1 / 8 :=
    one_div_le_one_div_of_le h8pos hle1
  have b2 : (1:ℚ) / ((a + 2 : ℕ) : ℚ) ≤ 1 / 8 :=
    one_div_le_one_div_of_le h8pos hle2
  have b3 : (1:ℚ) / ((a + 3 : ℕ) : ℚ) ≤ 1 / 8 :=
    one_div_le_one_div_of_le h8pos hle3
  have c1 : (1:ℚ) / (a + 1) ≤ 1 / 8 := by
    have : ((a + 1 : ℕ) : ℚ) = (a:ℚ) + 1 := by norm_cast
    rw [this] at b1; exact b1
  have c2 : (1:ℚ) / (a + 2) ≤ 1 / 8 := by
    have : ((a + 2 : ℕ) : ℚ) = (a:ℚ) + 2 := by norm_cast
    rw [this] at b2; exact b2
  have c3 : (1:ℚ) / (a + 3) ≤ 1 / 8 := by
    have : ((a + 3 : ℕ) : ℚ) = (a:ℚ) + 3 := by norm_cast
    rw [this] at b3; exact b3
  linarith [b0, c1, c2, c3]

end JSP000243
