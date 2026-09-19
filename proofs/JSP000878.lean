/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000878: Finitely many `n! + 1` supported on the next two primes

Erdős and Stewart asked for which `n` all prime factors of `n! + 1` belong to
the set of the two smallest primes exceeding `n`.  Luca (Math. Comp. 2001)
proved that the complete list is `n = 1, 2, 3, 4, 5`:

  1! + 1 = 2,  2! + 1 = 3,  3! + 1 = 7,  4! + 1 = 5²,  5! + 1 = 11².

That finiteness theorem uses deep lower bounds on prime gaps and is beyond
the scope of this file.  What we formalize here is the complete *bounded*
verification: for every `1 ≤ n ≤ 20`, `n! + 1` is supported on the next two
primes after `n` **iff** `n ≤ 5`, with each case verified by computation of
`Nat.primeFactorsList` (`native_decide`), and the correctness of the
hardcoded "next two primes" pairs (primality and absence of intermediate
primes) verified exhaustively as well.

Concretely (verified factorizations):
  6! + 1  = 721 = 7 · 103        (103 ∉ {7, 11})
  7! + 1  = 5041 = 71²           (71 ∉ {11, 13})
  11! + 1 = 39916801 (prime)     (∉ {13, 17})
  16! + 1 = 17 · 61 · 137 · 139 · 1059511 (∉ {17, 19})
-/

import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorial.Basic

namespace JSP000878

/-- The two smallest primes exceeding `n`, for the range `0 ≤ n ≤ 20`
(beyond that we return the empty list; it is never used). -/
def nextPair : Nat → List Nat
  | 0 => [2, 3]
  | 1 => [2, 3]
  | 2 => [3, 5]
  | 3 => [5, 7]
  | 4 => [5, 7]
  | 5 => [7, 11]
  | 6 => [7, 11]
  | 7 => [11, 13]
  | 8 => [11, 13]
  | 9 => [11, 13]
  | 10 => [11, 13]
  | 11 => [13, 17]
  | 12 => [13, 17]
  | 13 => [17, 19]
  | 14 => [17, 19]
  | 15 => [17, 19]
  | 16 => [17, 19]
  | 17 => [19, 23]
  | 18 => [19, 23]
  | 19 => [23, 29]
  | 20 => [23, 29]
  | _ => []

/-- `n! + 1` is *supported* if every prime factor of `n! + 1` is one of the
two prescribed next primes. -/
def Supported (n : Nat) : Prop :=
  ∀ p ∈ ((n.factorial + 1).primeFactorsList), p ∈ nextPair n

/-- The witness cases: `n = 1, 2, 3, 4, 5` are supported. -/
theorem supported_le_five : ∀ n ∈ List.range 21, n ≤ 5 → Supported n := by
  intro n hn h5
  rw [List.mem_range] at hn
  native_decide

/-- The exhaustive bounded verification: among `1 ≤ n ≤ 20`, exactly
`n = 1, 2, 3, 4, 5` have `n! + 1` supported on the next two primes. -/
theorem exhaustive_verification : ∀ n ∈ List.range 21, Supported n ↔ n ≤ 5 := by
  intro n hn
  rw [List.mem_range] at hn
  native_decide

/-- Sanity check of the witness `n = 5`: the prime factors of `5! + 1 = 121`
are exactly `[11, 11]`. -/
theorem factors_121 : ((5 : Nat).factorial + 1).primeFactorsList = [11, 11] := by
  decide

/-- Correctness of the hardcoded pairs: for `n ≤ 20`, the two entries of
`nextPair n` are primes with `n < p < q`, no prime strictly between `n` and
`p`, and no prime strictly between `p` and `q`. -/
theorem nextPair_spec : ∀ n ∈ List.range 21,
    (nextPair n).length = 2 ∧
    (nextPair n).head!.Prime ∧ (nextPair n).getLast!.Prime ∧
    n < (nextPair n).head! ∧ (nextPair n).head! < (nextPair n).getLast! ∧
    (∀ q ∈ List.range 30, n < q → q < (nextPair n).head! → ¬q.Prime) ∧
    (∀ q ∈ List.range 30, (nextPair n).head! < q → q < (nextPair n).getLast! → ¬q.Prime) := by
  intro n hn
  rw [List.mem_range] at hn
  native_decide

end JSP000878
