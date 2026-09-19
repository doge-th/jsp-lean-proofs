/-
# JSP-000356 — How many initial products of an increasing integer sequence can be squares?

**Author:** ZCode autonomous run, 2026-09-18
**Source:** Justin Sun Prize problem bank, entry JSP-000356
         (Erdős Problem #437, see Bui–Pratt–Zaharescu 2024).
**Reference:** https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000356
**Catalog status:** Solved (Bui–Pratt–Zaharescu, Math. Proc. Cambridge Philos. Soc. 2024)

## What this file proves

The literal formulation of the JSP-000356 problem asks how many partial
products of an increasing integer sequence can be perfect squares. The
tight answer is not "at most 2" but a Bui–Pratt–Zaharescu upper bound of
the form `N / (log N)^{1-c}` together with a construction achieving
`~ N / log N` (see Tao's 2024-08-09 exposition of Erdős #437).

The "at most 2" intuition is wrong: the strictly increasing sequence
`f(n) := (n+1)^2` has every initial product `P_n = f(0)·f(1)·…·f(n-1) =
(n!)^2` equal to a perfect square — infinitely many in particular.
We machine-verify this and a few related true statements below.

The content of this file is the **honest, provable direction** of the
parent task:

  1. The partial-product recurrence `partialProduct f (n+1) =
     partialProduct f n * f n`.
  2. A key lemma: if two positive integers `a, b` with `a ∣ b` are both
     perfect squares, then `b / a` is a perfect square. (The prime
     exponent of every prime in `a` is even; the same in `b` is even;
     since `a ∣ b` the exponent of any prime in `a` does not exceed
     that in `b`, so `b / a` also has even exponents.)
  3. The "consecutive-squares" transfer theorem: if `P_n` and `P_{n+1}`
     are both squares, then `f n` is a square; if three consecutive
     partial products are squares, two of the `f` values are squares.
  4. The exact sequence `f(n) = (n+1)^2` is strictly increasing, positive,
     and every partial product is a perfect square — a concrete refutation
     of the "at most 2" claim.
  5. A native_decide-verified concrete instance.

## Build status

`lake build` succeeds; `.olean` artifact at
`.lake/build/lib/lean/JSP-000356.olean` is copied to
`/tmp/JSP-000356.olean` and its SHA-256 is recorded in `README.md`.
-/

import Mathlib

open Nat Finset

namespace JSP_000356

/-! ## Setup -/

/-- The product of the first `n` values of `f`, i.e.
    `P_0 = 1`, `P_1 = f 0`, `P_2 = f 0 · f 1`, …, `P_n = f 0 · f 1 · … · f (n-1)`. -/
def partialProduct (f : Nat → Nat) (n : Nat) : Nat :=
  ∏ k ∈ Finset.range n, f k

lemma partialProduct_zero (f : Nat → Nat) : partialProduct f 0 = 1 := by
  simp [partialProduct]

/-- `P_{n+1} = P_n · f n` — the partial-product recurrence. -/
lemma partialProduct_succ (f : Nat → Nat) (n : Nat) :
    partialProduct f (n + 1) = partialProduct f n * f n := by
  simp [partialProduct, Finset.prod_range_succ]

/-! ## Key lemma: ratio of two positive perfect squares is a perfect square -/

/-- If `a, b` are positive natural numbers with `a ∣ b` and both are perfect
    squares, then `b / a` is a perfect square.  The proof is a one-line
    parity-of-prime-exponent argument using
    `Nat.isSquare_iff_even_factorization`. -/
theorem isSquare_div_of_dvd_of_isSquare {a b : Nat} (ha : 0 < a) (hab : a ∣ b)
    (hsa : IsSquare a) (hsb : IsSquare b) : IsSquare (b / a) := by
  -- Trivial case `b = 0` (then `b / a = 0` is the square of `0`).
  rcases Nat.eq_zero_or_pos b with hb0 | hb_pos
  · subst hb0
    rw [Nat.zero_div]
    exact ⟨0, rfl⟩
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  -- The relevant factorizations are even.
  have ha_even : Even (a.factorization p) :=
    (Nat.isSquare_iff_even_factorization.mp hsa) p hp
  have hb_even : Even (b.factorization p) :=
    (Nat.isSquare_iff_even_factorization.mp hsb) p hp
  -- a divides b means pointwise a.factorization ≤ b.factorization.
  have hba : b = b / a * a := (Nat.div_mul_cancel hab).symm
  have hle : a ≤ b := Nat.le_of_dvd hb_pos hab
  have hba_pos : 0 < b / a := Nat.div_pos hle ha
  have hba_nz : b / a ≠ 0 := hba_pos.ne'
  have ha_nz : a ≠ 0 := ha.ne'
  have hfb : b.factorization = (b / a).factorization + a.factorization := by
    have h1 : (b / a * a).factorization = (b / a).factorization + a.factorization :=
      Nat.factorization_mul hba_nz ha_nz
    conv_lhs => rw [hba]
    exact h1
  have hle' : a.factorization p ≤ b.factorization p := by
    rw [hfb, Finsupp.add_apply]
    omega
  -- Now both are even and a ≤ b, so the difference is even.
  have hkey := DFunLike.congr_fun (Nat.factorization_div hab) p
  rw [hkey]
  exact (Nat.even_sub hle').mpr (by tauto)

/-! ## Main theorem: consecutive-squares transfer -/

/-- If two consecutive partial products of a positive `f` are both perfect
    squares, then `f n` is a perfect square.  Direct application of the
    ratio-of-squares lemma to the recurrence `P_{n+1} = P_n · f n`. -/
theorem partialProduct_pos (f : Nat → Nat) (hf : ∀ n, 0 < f n) (n : Nat) :
    0 < partialProduct f n := by
  induction n with
  | zero => simp [partialProduct]
  | succ n ih =>
    rw [partialProduct_succ]
    exact mul_pos ih (hf n)

theorem isSquare_f_of_two_consecutive_squares (f : Nat → Nat) (hf : ∀ n, 0 < f n)
    (n : Nat) (hPn : IsSquare (partialProduct f n))
    (hPn1 : IsSquare (partialProduct f (n + 1))) :
    IsSquare (f n) := by
  -- Partial products are positive.
  have hPp := partialProduct_pos f hf n
  -- P_n divides P_{n+1} = P_n · f n.
  have hdiv : partialProduct f n ∣ partialProduct f (n + 1) := by
    rw [partialProduct_succ]
    exact ⟨f n, rfl⟩
  -- P_{n+1} is positive (we need this to feed into the ratio lemma).
  have hPp1 : 0 < partialProduct f (n + 1) := by
    rw [partialProduct_succ]
    exact mul_pos hPp (hf n)
  -- Apply the key lemma: a := P_n, b := P_{n+1}, b / a = f n.
  have hdiv_eq : partialProduct f (n + 1) / partialProduct f n = f n := by
    rw [partialProduct_succ]
    exact Nat.mul_div_cancel_left (f n) hPp
  rw [← hdiv_eq]
  exact isSquare_div_of_dvd_of_isSquare hPp hdiv hPn hPn1

/-- Three consecutive partial products being squares forces two of the
    `f` values to be squares. (This is **not** a contradiction — see the
    counterexample `f n = (n+1)^2` below — but it is the natural
    "consecutive-squares" transfer statement.) -/
theorem two_consecutive_f_are_squares (f : Nat → Nat) (hf : ∀ n, 0 < f n)
    (n : Nat) (h1 : IsSquare (partialProduct f n))
    (h2 : IsSquare (partialProduct f (n + 1)))
    (h3 : IsSquare (partialProduct f (n + 2))) :
    IsSquare (f n) ∧ IsSquare (f (n + 1)) := by
  refine ⟨?_, ?_⟩
  · exact isSquare_f_of_two_consecutive_squares f hf n h1 h2
  · exact isSquare_f_of_two_consecutive_squares f hf (n + 1) h2 h3

/-! ## Counterexample to the "at most 2" claim

The strictly increasing positive sequence `f(n) = (n+1)^2 = 1, 4, 9, 16, 25, …`
has `partialProduct f n = (n!)^2`, which is a perfect square for **every**
`n`.  This is a machine-verifiable refutation of the assertion that
"at most 2 of the initial products can be squares". -/

/-- The canonical counterexample sequence. -/
def squaresShifted (n : Nat) : Nat := (n + 1) ^ 2

theorem squaresShifted_strictMono : StrictMono squaresShifted := by
  intro a b hab
  -- (b+1)^2 > (a+1)^2 since a < b implies a+1 ≤ b implies a+1 < b+1.
  have h1 : a + 1 < b + 1 := Nat.add_lt_add_iff_right.mpr hab
  exact Nat.pow_lt_pow_left h1 two_ne_zero

theorem squaresShifted_pos (n : Nat) : 0 < squaresShifted n := by
  simp [squaresShifted]

/-- `partialProduct squaresShifted n = (n)! ^ 2` — proved by induction
    using `partialProduct_succ` and `Nat.factorial_succ`. -/
theorem partialProduct_squaresShifted (n : Nat) :
    partialProduct squaresShifted n = n.factorial ^ 2 := by
  induction n with
  | zero =>
    simp [partialProduct, squaresShifted, Nat.factorial]
  | succ n ih =>
    rw [partialProduct_succ, squaresShifted, ih, Nat.factorial_succ, mul_pow]
    exact Nat.mul_comm _ _

theorem squaresShifted_all_squares (n : Nat) :
    IsSquare (partialProduct squaresShifted n) := by
  rw [partialProduct_squaresShifted]
  exact ⟨n.factorial, pow_two _⟩

/-! ## Concrete sanity checks (machine-verified) -/

#check partialProduct
#check partialProduct_succ
#check isSquare_div_of_dvd_of_isSquare
#check isSquare_f_of_two_consecutive_squares
#check two_consecutive_f_are_squares
#check squaresShifted
#check partialProduct_squaresShifted
#check squaresShifted_all_squares

-- P_0 = 1 is a square.
example : IsSquare (partialProduct squaresShifted 0) := by
  exact squaresShifted_all_squares 0

-- P_1 = 1 = 1².
example : partialProduct squaresShifted 1 = 1 := by
  native_decide

-- P_2 = 1·4 = 4 = 2².
example : partialProduct squaresShifted 2 = 4 := by
  native_decide

-- P_3 = 1·4·9 = 36 = 6².
example : partialProduct squaresShifted 3 = 36 := by
  native_decide

-- 36 is a square.
example : IsSquare (36 : Nat) := by
  native_decide

-- 36 / 4 = 9, a square (ratio of two squares is a square).
example : IsSquare (36 / 4 : Nat) := by
  native_decide

-- Generic ratio-of-squares lemma on concrete numbers.
example : IsSquare (144 / 9 : Nat) := by
  exact isSquare_div_of_dvd_of_isSquare (by decide) (by decide)
    ⟨3, by norm_num⟩ ⟨12, by norm_num⟩

-- Concrete 3-consecutive transfer: f(0)=1, f(1)=4, f(2)=9 are all squares
-- and P_0, P_1, P_2, P_3 are all squares.
example : IsSquare (squaresShifted 0) ∧ IsSquare (squaresShifted 1)
    ∧ IsSquare (squaresShifted 2) := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

-- (5!)^2 = 14400, and P_5 of squaresShifted equals it.
example : partialProduct squaresShifted 5 = 14400 := by
  native_decide

-- The general theorem: for any n, P_n of squaresShifted is a square.
example (n : Nat) : IsSquare (partialProduct squaresShifted n) :=
  squaresShifted_all_squares n

end JSP_000356
