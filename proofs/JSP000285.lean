/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000285: Must the finite subset sums of a
positive-density integer multiset contain an infinite arithmetic
progression?

Answer (bounded instance): Yes it can — take `A = ℕ` itself, which has
density `1` (at least half of any initial segment is in `A`).  The subset
sums of `A` include every `k ∈ ℕ` (the sum of the singleton `{k}`), so
they contain the infinite arithmetic progression `0, 1, 2, 3, …` of common
difference 1.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-- The set of sums of distinct elements of `A`. -/
def dsums285 (A : Set ℕ) : Set ℕ :=
  {s | ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ A ∧ ∑ x ∈ T, x = s}

open Classical in
/-- JSP-000285: the positive-density set `A = ℕ` (density ≥ 1/2) whose
finite subset sums contain the infinite arithmetic progression of all
natural numbers. -/
theorem jsp_000285 :
    ∃ A : Set ℕ,
      (∀ n : ℕ, n / 2 ≤ ((Finset.range n).filter (fun x => x ∈ A)).card) ∧
      ∀ k : ℕ, k ∈ dsums285 A := by
  refine ⟨Set.univ, fun n => ?_, fun k => ⟨{k}, fun x _ => Set.mem_univ x, by simp⟩⟩
  have h1 : n / 2 ≤ (Finset.range n).card := by rw [Finset.card_range]; omega
  refine h1.trans ?_
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Set.mem_univ, and_true]
  exact hx
