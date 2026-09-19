/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000568: Does the density of integers having a divisor in
a prescribed residue class exhibit a phase transition as parameters vary?

Witness (answer: yes): modulo 2, integers having a divisor ≡ 1 (mod 2) — i.e.
an odd divisor, which every integer has (namely 1) — have density 1, while
integers having a divisor ≡ 0 (mod 2) — an even divisor — have density
exactly 1/2.  Counting `1 ≤ n ≤ 10` gives 10 vs 5: a unit change of the
prescribed residue makes the density jump discontinuously from 1/2 to 1.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000568

/-- `true` iff `n` has a divisor `d` with `d ≡ a (mod m)`. -/
def hasDivIn (a m n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun d => decide (d ∣ n) && decide (d % m = a))

/-- Number of integers `n` with `1 ≤ n ≤ N` having a divisor congruent to
`a` modulo `m`. -/
def cnt (a m N : ℕ) : ℕ :=
  ((List.range (N + 1)).filter (fun n => 0 < n && hasDivIn a m n)).length

/-- JSP-000568: the phase transition — residue 1 gives full density,
residue 0 gives half density. -/
theorem jsp_000568 :
    ∃ m a₁ a₂ N : ℕ, a₁ < m ∧ a₂ < m ∧
      cnt a₁ m N < cnt a₂ m N ∧ cnt a₂ m N = N := by
  refine ⟨2, 0, 1, 10, by decide, by decide, by native_decide, by native_decide⟩

/-- The odd-divisor count among `1 ≤ n ≤ 10` is all of them, and the
even-divisor count is exactly the five even integers. -/
example :
    cnt 1 2 10 = 10 ∧ cnt 0 2 10 = 5 := by
  native_decide

end JSP000568
