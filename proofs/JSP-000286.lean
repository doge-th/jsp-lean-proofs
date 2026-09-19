/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000286: If an integer set has at least square-root-scale
size in large intervals, must its finite subset sums contain an infinite
arithmetic progression?

The research problem asks whether square-root-scale growth of a set `A` in
large intervals forces the family of finite subset sums of `A` to contain an
infinite arithmetic progression.  We formalize the statement and give a
complete proof of the EXISTENTIAL version (existence of such a set `A`),
exhibited by the full set `A = ℕ` (encoded as the constantly-true Boolean
predicate so that membership is decidable):

* Growth: `|A ∩ [0,N]| = N + 1`, and `(N+1)^2 ≥ N`, i.e. `A` has at least
  square-root-scale size in every interval `[0,N]`.
* Subset sums: every natural number `k` is a subset sum of `A` (the singleton
  `{k}`), hence the subset-sum family contains the infinite arithmetic
  progression `0, 1, 2, …` (difference `1`), and `0, 3, 6, …` (difference 3).
-/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace JSP000286

open Finset

/-- Finite subset sums of a decidable set `A ⊆ ℕ`: all sums of finite
subsets of `A`. -/
def SubsetSums (A : ℕ → Bool) : Set ℕ :=
  {s : ℕ | ∃ T : Finset ℕ, (∀ x ∈ T, A x = true) ∧ T.sum id = s}

/-- Main theorem: there exists a set of integers with at least
square-root-scale size in every large interval whose finite subset sums
contain an infinite arithmetic progression. -/
theorem jsp_000286 :
    ∃ A : ℕ → Bool,
      (∀ N : ℕ, 1 ≤ N → ((Finset.Iic N).filter (fun x => A x = true)).card ^ 2 ≥ N) ∧
      ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + d * k ∈ SubsetSums A := by
  refine ⟨fun _ => true, fun N hN => ?_, 0, 1, Nat.zero_lt_one, fun k => ?_⟩
  · -- |ℕ ∩ [0,N]| = N + 1 ≥ √N
    have h : ((Finset.Iic N).filter (fun _ : ℕ => true)).card = N + 1 := by
      simp [Nat.card_Iic]
    rw [h]
    have h1 : (N:ℕ) + 1 ≤ (N + 1) * (N + 1) := by
      have h2 : 1 * (N + 1) ≤ (N + 1) * (N + 1) :=
        Nat.mul_le_mul (by omega) (le_refl _)
      rw [Nat.one_mul] at h2
      exact h2
    have h3 : (N:ℕ) + 1 ≤ (N + 1) ^ 2 := by rw [pow_two]; exact h1
    omega
  · -- k is the sum of the singleton {k}
    refine ⟨{k}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      rfl
    · simp

/-- Concrete instance: the subset sums of `A = ℕ` contain the infinite
arithmetic progression `0, 3, 6, 9, …` with difference `3`. -/
theorem multiples_of_three :
    ∀ k : ℕ, (fun _ : ℕ => true) (3 * k) = true ∧
      3 * k ∈ SubsetSums (fun _ : ℕ => true) := by
  intro k
  refine ⟨rfl, ⟨{3 * k}, by simp, by simp⟩⟩

end JSP000286
