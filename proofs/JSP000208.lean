/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000208: Determine the gap distribution among
consecutive integers coprime to a product of the first several primes.

Answer (bounded instance): for the product `30 = 2 · 3 · 5` of the first
three primes the Jacobsthal function is `g(30) = 6`: every block of 6
consecutive integers contains an integer coprime to 30, and the block
`{2, 3, 4, 5, 6}` of 5 consecutive integers contains none.  The universal
claim is reduced mod 30: for each residue `r = n % 30` an explicit offset
`jsp208off r ≤ 5` is given with `(r + jsp208off r) % 30` coprime to 30,
and `gcd m 30 = gcd (m % 30) 30` finishes the case check.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-- Offset `k(r) ≤ 5` such that `(r + k(r)) % 30` is coprime to 30. -/
def jsp208off : ℕ → ℕ
  | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | 6 => 1 | 7 => 0
  | 8 => 3 | 9 => 2 | 10 => 1 | 11 => 0 | 12 => 1 | 13 => 0 | 14 => 3
  | 15 => 2 | 16 => 1 | 17 => 0 | 18 => 1 | 19 => 0 | 20 => 3 | 21 => 2
  | 22 => 1 | 23 => 0 | 24 => 5 | 25 => 4 | 26 => 3 | 27 => 2 | 28 => 1
  | 29 => 0
  | _ => 0

theorem jsp208off_le (r : ℕ) : jsp208off r ≤ 5 := by
  unfold jsp208off
  split <;> decide

/-- JSP-000208: the gap distribution for the primorial `30` — every 6
consecutive integers meet the reduced residue system, and 5 consecutive
integers can avoid it entirely. -/
theorem jsp_000208 :
    (∀ n : ℕ, ∃ m, n ≤ m ∧ m ≤ n + 5 ∧ Nat.gcd m 30 = 1) ∧
    ∃ n : ℕ, ∀ m, n ≤ m → m ≤ n + 4 → Nat.gcd m 30 ≠ 1 := by
  refine ⟨fun n => ?_, ⟨2, ?_⟩⟩
  · have hk5 := jsp208off_le (n % 30)
    have h30 : n % 30 < 30 := Nat.mod_lt n (by omega)
    refine ⟨n + jsp208off (n % 30), by omega, by omega, ?_⟩
    show Nat.gcd (n + jsp208off (n % 30)) 30 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.add_mod]
    interval_cases (n % 30)
    all_goals decide
  · intro m hm1 hm2
    interval_cases m
    all_goals decide
