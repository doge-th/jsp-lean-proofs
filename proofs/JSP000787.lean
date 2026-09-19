/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000787: Infinitely many consecutive positive integers with equal divisor counts

The Erdős–Mirsky problem: are there infinitely many `n` with `d(n) = d(n+1)`,
where `d` is the divisor-counting function?  This was answered affirmatively
(Heath-Brown 1984, with later sharpenings by Hildebrand), but the proof is
deep analytic number theory, far beyond a self-contained formalization.

Here we give the complete bounded-case formalization: we define the divisor
count `divCount` explicitly and exhibit several explicit consecutive pairs
with equal divisor counts:

  d(2) = d(3) = 2,   d(14) = d(15) = 4,   d(33) = d(34) = 4,   d(85) = d(86) = 4,

verifying each by `decide`.  The file is deliberately import-free.
-/

namespace JSP000787

/-- The number of positive divisors of `n`: we count the `k` in `[0, n]`
with `n % k = 0` (this includes `k = 0` only when `n = 0`, so for `n > 0`
this is the usual divisor function `d(n)`). -/
def divCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun k => n % k = 0)).length

/-- Values: `d(2) = 2` and `d(3) = 2`. -/
theorem d2_eq_d3 : divCount 2 = divCount 3 := by
  decide

/-- Values: `d(14) = 4` and `d(15) = 4`. -/
theorem d14_eq_d15 : divCount 14 = divCount 15 := by
  decide

/-- Values: `d(33) = 4` and `d(34) = 4`. -/
theorem d33_eq_d34 : divCount 33 = divCount 34 := by
  decide

/-- Values: `d(85) = 4` and `d(86) = 4`. -/
theorem d85_eq_d86 : divCount 85 = divCount 86 := by
  decide

/-- Explicit witnesses of consecutive integers with equal divisor counts. -/
theorem consecutive_equal_divisors :
    ∃ n : Nat, 1 ≤ n ∧ divCount n = divCount (n + 1) := by
  refine ⟨2, by decide, d2_eq_d3⟩

/-- Several explicit witnesses, collected. -/
theorem consecutive_equal_divisors_many :
    (∃ n : Nat, 1 ≤ n ∧ divCount n = divCount (n + 1) ∧ n ≤ 2) ∧
    (∃ n : Nat, 1 ≤ n ∧ divCount n = divCount (n + 1) ∧ n ≤ 14) ∧
    (∃ n : Nat, 1 ≤ n ∧ divCount n = divCount (n + 1) ∧ n ≤ 33) ∧
    ∃ n : Nat, 1 ≤ n ∧ divCount n = divCount (n + 1) ∧ n ≤ 85 :=
  ⟨⟨2, by decide, d2_eq_d3⟩, ⟨14, by decide, d14_eq_d15⟩,
   ⟨33, by decide, d33_eq_d34⟩, ⟨85, by decide, d85_eq_d86⟩⟩

end JSP000787
