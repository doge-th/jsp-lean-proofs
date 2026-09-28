/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000598 (Erdős Problem #730):

  "Can two distinct central binomial coefficients have exactly the same
   prime divisors?"

Equivalently (Erdős–Graham–Ruzsa–Straus, 1975): are there integers `m ≠ n` with
`C(2m, m)` and `C(2n, n)` having the same set of prime divisors?

This file proves the finite / existential content of the problem completely,
together with the general structural lemmas that the reference solution relies
on, namely

* Kummer's bound: a prime dividing `C(2n, n)` is at most `2n` (`dvd_B_le`);
* the central-binomial recurrence `B (n+1) * (n+1) = B n * (2*(2n+1))`, the
  algebraic mechanism behind every known construction;
* the two concrete Erdős–Graham–Ruzsa–Straus examples `(87, 88)` and
  `(607, 608)`, with their prime divisor sets computed *exactly*.

The main theorems `jsp598_yes` and `jsp598_support_87_88` answer the catalog question
"yes", with an explicit witness.

SCOPE NOTE (deliberate, not hidden): the asymptotic claim of the additional
GPT-Pro write-up cited by the catalog (a positive lower density of `x` with
`rad C(2n_x, n_x) = rad C(2n_x+2, n_x+1)`, i.e. infinitely many such pairs) is
a research-level analytic number theory argument (Kummer carries, restricted
base-`p` digit sets, CRT counting, a first-moment estimate) and is NOT
formalised here.  Only the concrete/finite content is machine-checked.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JSP598

open Nat

/-! ## 1. Definitions -/

/-- `B n` is the `n`-th central binomial coefficient `C(2n, n)`. -/
def B (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- `SamePrimeSupport m n` says that the central binomial coefficients `C(2m, m)`
and `C(2n, n)` have exactly the same set of prime divisors. -/
def SamePrimeSupport (m n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (p ∣ B m ↔ p ∣ B n)

/-! ## 2. General lemmas -/

/-! ### 2.1. Kummer's bound: prime divisors of `C(2n, n)` are bounded by `2n` -/

theorem dvd_factorial_le {p n : ℕ} (hp : p.Prime) (h : p ∣ Nat.factorial n) : p ≤ n := by
  induction n with
  | zero =>
      have h1 : p = 1 := by simpa using h
      exact absurd h1 hp.ne_one
  | succ k ih =>
      rw [Nat.factorial_succ] at h
      rcases hp.dvd_mul.mp h with h1 | h1
      · exact Nat.le_of_dvd (Nat.zero_lt_succ k) h1
      · exact Nat.le_trans (Nat.le_succ _) (Nat.succ_le_succ (ih h1))

/-- **Kummer's bound.** Every prime divisor of the central binomial coefficient
`C(2n, n)` is at most `2n`.  Consequently only finitely many primes can divide a
given `B n`, which is what makes the exact computations below possible. -/
theorem dvd_B_le {p n : ℕ} (hp : p.Prime) (h : p ∣ B n) : p ≤ 2 * n := by
  have hkn : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by norm_num)
  have hf : (Nat.choose (2 * n) n * Nat.factorial n) * Nat.factorial (2 * n - n)
      = Nat.factorial (2 * n) :=
    Nat.choose_mul_factorial_mul_factorial hkn
  have h2 : p ∣ Nat.factorial (2 * n) := by
    rw [← hf]
    exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right_of_dvd h _) _
  exact dvd_factorial_le hp h2

/-! ### 2.2. The central-binomial recurrence

`B (n+1) / B n = 2(2n+1)/(n+1)`.  This is the algebraic engine behind every
construction of equal prime supports: when one passes from `B n` to `B (n+1)`,
the only primes that can gain or lose membership in the prime support are those
dividing `n+1` or `2n+1` (the reference solution's "transition criterion"). -/

theorem B_succ_mul (n : ℕ) :
    Nat.choose (2 * (n + 1)) (n + 1) * (n + 1) = Nat.choose (2 * n) n * (2 * (2 * n + 1)) := by
  have hkn1 : n + 1 ≤ 2 * (n + 1) := by omega
  have hkn2 : n ≤ 2 * n := by omega
  have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
  have hs1 : (2 * (n + 1)) - (n + 1) = n + 1 := by omega
  have hs2 : (2 * n) - n = n := by omega
  have hA : Nat.factorial (2 * n + 2) = (2 * n + 2) * Nat.factorial (2 * n + 1) :=
    Nat.factorial_succ (2 * n + 1)
  have hB : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) :=
    Nat.factorial_succ (2 * n)
  have hf2 : Nat.factorial (2 * (n + 1))
      = Nat.factorial (2 * n) * (2 * n + 2) * (2 * n + 1) := by
    rw [h2, hA, hB]; ac_rfl
  have hf1 : Nat.factorial (n + 1) = Nat.factorial n * (n + 1) := by
    rw [Nat.factorial_succ, Nat.mul_comm]
  -- the two `choose * k! * (N-k)! = N!` identities, in simplified form
  have ha : (Nat.choose (2 * (n + 1)) (n + 1) * Nat.factorial (n + 1))
      * Nat.factorial (n + 1) = Nat.factorial (2 * (n + 1)) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * (n + 1)) (k := n + 1) hkn1
    rw [hs1] at h
    exact h
  have hb : (Nat.choose (2 * n) n * Nat.factorial n) * Nat.factorial n
      = Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) hkn2
    rw [hs2] at h
    exact h
  -- step 1: express `B (n+1)` through `B n`
  have key : Nat.choose (2 * (n + 1)) (n + 1)
      * (Nat.factorial (n + 1) * Nat.factorial (n + 1))
      = Nat.choose (2 * n) n * (Nat.factorial n * Nat.factorial n)
        * ((2 * (n + 1)) * (2 * n + 1)) := by
    calc Nat.choose (2 * (n + 1)) (n + 1) * (Nat.factorial (n + 1) * Nat.factorial (n + 1))
        = (Nat.choose (2 * (n + 1)) (n + 1) * Nat.factorial (n + 1))
          * Nat.factorial (n + 1) := by ac_rfl
      _ = Nat.factorial (2 * (n + 1)) := ha
      _ = Nat.factorial (2 * n) * (2 * n + 2) * (2 * n + 1) := hf2
      _ = _ := by
        have h := hb
        rw [← h, h2]
        ac_rfl
  -- step 2: substitute `(n+1)! = n! * (n+1)` and rebracket the square
  have hsq : (Nat.factorial n * (n + 1)) * (Nat.factorial n * (n + 1))
      = (Nat.factorial n * Nat.factorial n) * ((n + 1) * (n + 1)) := by
    ac_rfl
  have key' : Nat.choose (2 * (n + 1)) (n + 1)
      * ((Nat.factorial n * (n + 1)) * (Nat.factorial n * (n + 1)))
      = Nat.choose (2 * n) n * (Nat.factorial n * Nat.factorial n)
        * ((2 * (n + 1)) * (2 * n + 1)) := by
    rw [← hf1]; exact key
  have key'' : Nat.choose (2 * (n + 1)) (n + 1)
      * ((Nat.factorial n * Nat.factorial n) * ((n + 1) * (n + 1)))
      = Nat.choose (2 * n) n * (Nat.factorial n * Nat.factorial n)
        * ((2 * (n + 1)) * (2 * n + 1)) := by
    rw [← hsq]; exact key'
  -- step 3: cancel the square `n! * n!`
  have hstep : (Nat.choose (2 * (n + 1)) (n + 1) * ((n + 1) * (n + 1)))
        * (Nat.factorial n * Nat.factorial n)
      = (Nat.choose (2 * n) n * ((2 * (n + 1)) * (2 * n + 1)))
        * (Nat.factorial n * Nat.factorial n) := by
    calc (Nat.choose (2 * (n + 1)) (n + 1) * ((n + 1) * (n + 1)))
        * (Nat.factorial n * Nat.factorial n)
      = Nat.choose (2 * (n + 1)) (n + 1)
        * ((Nat.factorial n * Nat.factorial n) * ((n + 1) * (n + 1))) := by ac_rfl
      _ = Nat.choose (2 * n) n * (Nat.factorial n * Nat.factorial n)
        * ((2 * (n + 1)) * (2 * n + 1)) := key''
      _ = (Nat.choose (2 * n) n * ((2 * (n + 1)) * (2 * n + 1)))
        * (Nat.factorial n * Nat.factorial n) := by ac_rfl
  have hz1 : (2 * (n + 1)) * (2 * n + 1) = (2 * (2 * n + 1)) * (n + 1) := by ac_rfl
  have e1 : Nat.choose (2 * (n + 1)) (n + 1) * ((n + 1) * (n + 1))
      = Nat.choose (2 * n) n * ((2 * (2 * n + 1)) * (n + 1)) := by
    have h := Nat.mul_right_cancel
      (Nat.mul_pos (Nat.factorial_pos n) (Nat.factorial_pos n)) hstep
    rw [hz1] at h
    exact h
  -- step 4: cancel one factor `n + 1`
  have h1 : (Nat.choose (2 * (n + 1)) (n + 1) * (n + 1)) * (n + 1)
      = (Nat.choose (2 * n) n * (2 * (2 * n + 1))) * (n + 1) := by
    calc (Nat.choose (2 * (n + 1)) (n + 1) * (n + 1)) * (n + 1)
        = Nat.choose (2 * (n + 1)) (n + 1) * ((n + 1) * (n + 1)) := Nat.mul_assoc _ _ _
      _ = Nat.choose (2 * n) n * ((2 * (2 * n + 1)) * (n + 1)) := e1
      _ = (Nat.choose (2 * n) n * (2 * (2 * n + 1))) * (n + 1) := (Nat.mul_assoc _ _ _).symm
  exact Nat.mul_right_cancel (Nat.zero_lt_succ _) h1

/-! ## 3. The first Erdős–Graham–Ruzsa–Straus example: `(87, 88)` -/

/-- `C(174, 87) = 1446307705450557558142084756547133980616347954754720`. -/
theorem choose_174_87 :
    Nat.choose 174 87 = 1446307705450557558142084756547133980616347954754720 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  decide

/-- `C(176, 88) = 5752360192132899378974200736267010150178656638229000`. -/
theorem choose_176_88 :
    Nat.choose 176 88 = 5752360192132899378974200736267010150178656638229000 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  decide

theorem B_87 : B 87 = 1446307705450557558142084756547133980616347954754720 := by
  unfold B; exact choose_174_87

theorem B_88 : B 88 = 5752360192132899378974200736267010150178656638229000 := by
  unfold B; exact choose_176_88

/-- The exact set of prime divisors of `C(174, 87)` and of `C(176, 88)`. -/
def support_87 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173}

theorem support_87_dvd_B_87 : ∀ p ∈ support_87, p ∣ B 87 := by
  rw [B_87]
  decide

theorem dvd_B_87_of_prime {p : ℕ} (hp : p.Prime) (h : p ∣ B 87) : p ∈ support_87 := by
  have hle : p ≤ 174 := dvd_B_le hp h
  rw [B_87] at h
  interval_cases p
  all_goals first
    | decide
    | (exact absurd h (by decide))
    | (exact absurd hp (by decide))

theorem mem_support_87_iff {p : ℕ} (hp : p.Prime) : p ∈ support_87 ↔ p ∣ B 87 :=
  ⟨support_87_dvd_B_87 p, dvd_B_87_of_prime hp⟩

theorem support_87_dvd_B_88 : ∀ p ∈ support_87, p ∣ B 88 := by
  rw [B_88]
  decide

theorem dvd_B_88_of_prime {p : ℕ} (hp : p.Prime) (h : p ∣ B 88) : p ∈ support_87 := by
  have hle : p ≤ 176 := dvd_B_le hp h
  rw [B_88] at h
  interval_cases p
  all_goals first
    | decide
    | (exact absurd h (by decide))
    | (exact absurd hp (by decide))

theorem mem_support_88_iff {p : ℕ} (hp : p.Prime) : p ∈ support_87 ↔ p ∣ B 88 :=
  ⟨support_87_dvd_B_88 p, dvd_B_88_of_prime hp⟩

/-- **The Erdős–Graham–Ruzsa–Straus example `(87, 88)`.**
`C(174, 87)` and `C(176, 88)` have exactly the same prime divisors. -/
theorem jsp598_example_87_88 : SamePrimeSupport 87 88 := by
  intro p hp
  constructor
  · intro h
    exact (mem_support_88_iff hp).mp ((mem_support_87_iff hp).mpr h)
  · intro h
    exact (mem_support_87_iff hp).mp ((mem_support_88_iff hp).mpr h)

/-! ## 4. The second Erdős–Graham–Ruzsa–Straus example: `(607, 608)` -/

/-- `C(1214, 607)`. -/
theorem choose_1214_607 :
    Nat.choose 1214 607 =
      6458862209338074830570593682599956002542091117990392156950561561578766893609647622510260533613381713418584381671350413603590143386041437396831661491181913864709577363307741699380497177863781439399406631912919762020860189851047336297790250372001272029785119753116401435355424925599501420397283623467920589146167256208774311910740543420216502324584595457421589763200 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  decide

/-- `C(1216, 608)`. -/
theorem choose_1216_608 :
    Nat.choose 1216 608 =
      25814202580084739865602866198549166260160002330126073916759645714862505841235927175493311014277167045406513235956219580685401395440922192227468647078243504426388606896114822910352973918106889634441707426888807601497845824569153005269128796717044557619042501644856670210384346330932217847969406587215537880962477685176515753195887369261720560277533827239365893297000 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  decide

theorem B_607 : B 607 =
      6458862209338074830570593682599956002542091117990392156950561561578766893609647622510260533613381713418584381671350413603590143386041437396831661491181913864709577363307741699380497177863781439399406631912919762020860189851047336297790250372001272029785119753116401435355424925599501420397283623467920589146167256208774311910740543420216502324584595457421589763200 := by
  unfold B; exact choose_1214_607

theorem B_608 : B 608 =
      25814202580084739865602866198549166260160002330126073916759645714862505841235927175493311014277167045406513235956219580685401395440922192227468647078243504426388606896114822910352973918106889634441707426888807601497845824569153005269128796717044557619042501644856670210384346330932217847969406587215537880962477685176515753195887369261720560277533827239365893297000 := by
  unfold B; exact choose_1216_608

/-- The exact (common) set of 135 prime divisors of `C(1214, 607)` and `C(1216, 608)`. -/
def support_607 : Finset ℕ :=
  {2, 3, 5, 7, 13, 17, 19, 29, 31, 41,
   47, 61, 71, 79, 89, 103, 107, 109, 127, 131,
   157, 163, 167, 173, 211, 223, 227, 229, 233, 239,
   241, 307, 311, 313, 317, 331, 337, 347, 349, 353,
   359, 367, 373, 379, 383, 389, 397, 401, 613, 617,
   619, 631, 641, 643, 647, 653, 659, 661, 673, 677,
   683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
   757, 761, 769, 773, 787, 797, 809, 811, 821, 823,
   827, 829, 839, 853, 857, 859, 863, 877, 881, 883,
   887, 907, 911, 919, 929, 937, 941, 947, 953, 967,
   971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
   1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
   1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
   1181, 1187, 1193, 1201, 1213}

theorem support_607_dvd_B_607 : ∀ p ∈ support_607, p ∣ B 607 := by
  rw [B_607]
  decide

theorem dvd_B_607_of_prime {p : ℕ} (hp : p.Prime) (h : p ∣ B 607) : p ∈ support_607 := by
  have hle : p ≤ 1214 := dvd_B_le hp h
  rw [B_607] at h
  interval_cases p
  all_goals first
    | decide
    | (exact absurd h (by decide))
    | (exact absurd hp (by decide))

theorem mem_support_607_iff {p : ℕ} (hp : p.Prime) : p ∈ support_607 ↔ p ∣ B 607 :=
  ⟨support_607_dvd_B_607 p, dvd_B_607_of_prime hp⟩

theorem support_607_dvd_B_608 : ∀ p ∈ support_607, p ∣ B 608 := by
  rw [B_608]
  decide

theorem dvd_B_608_of_prime {p : ℕ} (hp : p.Prime) (h : p ∣ B 608) : p ∈ support_607 := by
  have hle : p ≤ 1216 := dvd_B_le hp h
  rw [B_608] at h
  interval_cases p
  all_goals first
    | decide
    | (exact absurd h (by decide))
    | (exact absurd hp (by decide))

theorem mem_support_608_iff {p : ℕ} (hp : p.Prime) : p ∈ support_607 ↔ p ∣ B 608 :=
  ⟨support_607_dvd_B_608 p, dvd_B_608_of_prime hp⟩

/-- **The Erdős–Graham–Ruzsa–Straus example `(607, 608)`.**
`C(1214, 607)` and `C(1216, 608)` have exactly the same prime divisors. -/
theorem jsp598_example_607_608 : SamePrimeSupport 607 608 := by
  intro p hp
  constructor
  · intro h
    exact (mem_support_608_iff hp).mp ((mem_support_607_iff hp).mpr h)
  · intro h
    exact (mem_support_607_iff hp).mp ((mem_support_608_iff hp).mpr h)

/-! ## 5. The answer to JSP-000598 -/

/-- **JSP-000598 / Erdős Problem #730 — answer: YES.**
There exist distinct `m ≠ n` such that `C(2m, m)` and `C(2n, n)` have exactly
the same set of prime divisors.  Witness: `m = 87`, `n = 88`. -/
theorem jsp598_yes :
    ∃ m n : ℕ, m ≠ n ∧ ∀ p : ℕ, p.Prime →
      (p ∣ Nat.choose (2 * m) m ↔ p ∣ Nat.choose (2 * n) n) :=
  ⟨87, 88, by norm_num, fun _ hp => jsp598_example_87_88 _ hp⟩

/-- The same answer with the central binomial coefficient notation `B`. -/
theorem jsp598_yes' : ∃ m n : ℕ, m < n ∧ SamePrimeSupport m n :=
  ⟨87, 88, by norm_num, jsp598_example_87_88⟩

/-- The complete prime-divisor data for the witness pair `(87, 88)`. -/
theorem jsp598_support_87_88 (p : ℕ) (hp : p.Prime) :
    (p ∣ Nat.choose 174 87 ↔ p ∈ support_87) ∧
      (p ∣ Nat.choose 176 88 ↔ p ∈ support_87) :=
  ⟨(mem_support_87_iff hp).symm, (mem_support_88_iff hp).symm⟩

/-! ## 6. Kernel audit: no `native_decide`, standard axioms only -/

#print axioms jsp598_yes
#print axioms jsp598_yes'
#print axioms jsp598_support_87_88
#print axioms jsp598_example_87_88
#print axioms jsp598_example_607_608
#print axioms dvd_B_le
#print axioms B_succ_mul

end JSP598
