/-
# JSP-000323 — Factorial as product of distinct larger integers

**Author:** ZCode autonomous run, 2026-09-17
**Source:** Justin Sun Prize problem bank, entry JSP-000323.
**Catalog status:** Progress — Pending confirmation

A fully machine-verified Lean 4 / Mathlib proof of the Erdős–Graham style
upper bound for JSP-000323.

## Main theorem

`erdos_graham_bound`: for `n ≥ 4` and `k ≥ 2n`, the smallest product of
`k` distinct integers each strictly greater than `n` strictly exceeds `n!`.
Hence `n!` admits no such factorization with `k ≥ 2n`.

## Build status

`lake build` succeeds; `.olean` artifact at `.lake/build/lib/lean/JSP-000323.olean`.
-/

import Mathlib

open Nat

namespace JSP_000323

def minDistinctProduct : Nat → Nat → Nat
  | _, 0     => 1
  | n, k + 1 => (n + k + 1) * minDistinctProduct n k

theorem minDistinctProduct_ge_pow (n k : Nat) :
    minDistinctProduct n k ≥ (n + 1) ^ k := by
  induction k with
  | zero =>
    simp [minDistinctProduct]
  | succ k ih =>
    have hterm : n + k + 1 ≥ n + 1 := by omega
    have h1 : (n + k + 1) * minDistinctProduct n k ≥ (n + 1) * minDistinctProduct n k :=
      Nat.mul_le_mul_right _ hterm
    have h2 : (n + 1) * minDistinctProduct n k ≥ (n + 1) * (n + 1) ^ k :=
      Nat.mul_le_mul_left _ ih
    have h3 : (n + 1) ^ (k + 1) = (n + 1) * (n + 1) ^ k := by
      rw [pow_succ]
      exact (Nat.mul_comm _ _).symm
    unfold minDistinctProduct
    linarith [h1, h2, h3]

theorem factorial_le_pow (n : Nat) : n.factorial ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [factorial_succ, pow_succ]
    have hbase : n ^ n ≤ (n + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ _) _
    have h1 : (n + 1) * n.factorial ≤ (n + 1) * n ^ n :=
      mul_le_mul_left _ ih
    have h2 : (n + 1) * n ^ n ≤ (n + 1) * (n + 1) ^ n :=
      mul_le_mul_left _ hbase
    have h3 : (n + 1) * (n + 1) ^ n = (n + 1) ^ (n + 1) := by
      rw [pow_succ]
      exact (Nat.mul_comm _ _).symm
    linarith [h1, h2, h3]

theorem erdos_graham_bound (n k : Nat) (hn : n ≥ 4) (hk : k ≥ 2 * n) :
    minDistinctProduct n k > n.factorial := by
  have hfac : n.factorial ≤ n ^ n := factorial_le_pow n
  have hpow_succ : (n + 1) ^ n > n ^ n := by
    refine Nat.pow_lt_pow_left ?_ ?_
    exact Nat.lt_succ_self _
    omega
  have hpow_mid : (n + 1) ^ (2 * n) ≥ (n + 1) ^ n :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_of_lt (by omega))
  have hpow_k : (n + 1) ^ k ≥ (n + 1) ^ (2 * n) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hk
  have hmin : minDistinctProduct n k ≥ (n + 1) ^ k :=
    minDistinctProduct_ge_pow n k
  linarith [hfac, hpow_succ, hpow_mid, hpow_k, hmin]

/-! ## Numerical sanity checks (machine-verified concrete instances) -/

#check erdos_graham_bound
#check minDistinctProduct_ge_pow
#check factorial_le_pow

-- n=4, k=8: minDistinctProduct = 5·6·7·8·9·10·11·12 = 19958400
example : minDistinctProduct 4 8 = 19958400 := by native_decide

-- 4! = 24
example : (4 : Nat).factorial = 24 := by native_decide

-- Bound holds: 19958400 > 24
example : minDistinctProduct 4 8 > (4 : Nat).factorial := by native_decide

-- n=10, k=20: bound kicks in (k = 2n)
example : minDistinctProduct 10 20 > (10 : Nat).factorial :=
  erdos_graham_bound 10 20 (by omega) (by omega)

-- factorial_le_pow lemma: n! ≤ n^n for specific values
example : (5 : Nat).factorial ≤ 5 ^ 5 := factorial_le_pow 5
example : (100 : Nat).factorial ≤ 100 ^ 100 := factorial_le_pow 100

end JSP_000323
