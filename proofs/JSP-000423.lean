/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000423: Does a power series with randomly signed
coefficients converge at some point of the unit circle?

No — and this holds for EVERY sign pattern, which is stronger than any
almost-sure statement: for coefficients `a_n = ±1` and `|z| = 1` the terms
`a_n · z^n` all have modulus exactly `1`, so they cannot tend to zero, and a
series whose terms do not tend to zero cannot converge.  We prove this in
full generality: for every sign sequence and every point of the unit circle,
the sequence of partial sums of `∑ a_n z^n` does not converge.

The proof observes that if the partial sums converged to some limit `L`,
then the differences of consecutive partial sums — which are exactly the
terms `a_N z^N` — would tend to `L - L = 0`; but those terms have constant
modulus `1 = |a_N| · ‖z‖^N`.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace JSP000423

open Finset Metric Filter

/-- The partial sums of a signed power series at `z`. -/
def partialSums (a : ℕ → ℤ) (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, (a n : ℂ) * z ^ n

/-- Terms of a signed series at a unit-circle point have modulus exactly 1. -/
theorem term_norm (a : ℕ → ℤ) (ha : ∀ n, |a n| = 1) (z : ℂ) (hz : ‖z‖ = 1)
    (N : ℕ) : ‖(a N : ℂ) * z ^ N‖ = 1 := by
  have hN : a N = 1 ∨ a N = -1 := eq_or_eq_neg_of_abs_eq (ha N)
  rcases hN with h | h
  · rw [h]; simp [norm_pow, hz, one_pow]
  · rw [h]; simp [norm_pow, hz, one_pow]

/-- Main theorem: a power series with coefficients `a_n = ±1` diverges at
every point of the unit circle. -/
theorem jsp_000423 :
    ∀ a : ℕ → ℤ, (∀ n, |a n| = 1) →
      ∀ z : ℂ, z ∈ sphere (0:ℂ) 1 →
        ¬ ∃ L : ℂ, Tendsto (partialSums a z) atTop (nhds L) := by
  intro a ha z hz ⟨L, hL⟩
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  -- Partial sums at N+1 also converge to L.
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have h1 : Tendsto (fun N => partialSums a z (N + 1)) atTop (nhds L) := hL.comp hshift
  -- Hence the terms (differences of consecutive partial sums) tend to zero.
  have hterm : Tendsto (fun N => (a N : ℂ) * z ^ N) atTop (nhds 0) := by
    have hd := h1.sub hL
    simpa [partialSums, Finset.sum_range_succ] using hd
  -- Their norms are constantly 1, contradiction with norm → 0.
  have hnorm0 : Tendsto (fun N => ‖(a N : ℂ) * z ^ N‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hterm
  have hconst : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 0) := by
    simpa only [term_norm a ha z hz1] using hnorm0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hconst)

end JSP000423
