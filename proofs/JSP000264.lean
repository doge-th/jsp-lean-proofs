/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000264: Does every assignment of signs to the
specified reciprocal set admit a nonempty zero-sum subset?

Answer: No.  For the reciprocal set `{1, 1/2, 1/3, 1/4, 1/5, 1/6}` (scaled
by `L = 60`, i.e. the integer set `{60, 30, 20, 15, 12, 10}`), the
all-plus sign assignment `σ ≡ 1` admits no nonempty zero-sum subset:
every nonempty subset sum is strictly positive.  Hence the statement
"every assignment of signs admits a nonempty zero-sum subset" is false.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-- A finset of positive integers has positive sum. -/
theorem lt_int_sum264 {S : Finset ℤ} (hpos : ∀ x ∈ S, 0 < x)
    (hne : S.Nonempty) : 0 < S.sum id := by
  classical
  revert hpos hne
  induction S using Finset.induction with
  | empty => intro _ hne; exact absurd hne (by simp)
  | insert a S ha ih =>
    intro hpos hne
    rw [Finset.sum_insert ha]
    rcases S.eq_empty_or_nonempty with h0 | hne'
    · subst h0
      simp only [Finset.sum_empty, add_zero]
      exact hpos a (Finset.mem_insert_self a ∅)
    · have h1 := ih (fun x hx => hpos x (Finset.mem_insert_of_mem hx)) hne'
      have h2 := hpos a (Finset.mem_insert_self a S)
      exact add_pos h2 h1

/-- JSP-000264: the all-plus assignment of signs to the reciprocal set
`{1, 1/2, …, 1/6}` (scaled by 60) admits no nonempty zero-sum subset. -/
theorem jsp_000264 :
    ∃ R : Finset ℤ, R.Nonempty ∧ ∃ σ : ℤ → ℤ,
      (∀ x ∈ R, σ x = 1 ∨ σ x = -1) ∧
      ∀ S, S ⊆ R → S.Nonempty → (∑ x ∈ S, σ x * x) ≠ 0 := by
  refine ⟨{60, 30, 20, 15, 12, 10}, ⟨60, by simp⟩, fun _ => 1, ?_, ?_⟩
  · intro x _
    exact Or.inl rfl
  · intro S hSR ⟨x₀, hx₀⟩
    have hxpos : 0 < x₀ := by
      have hx := hSR hx₀
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    rw [Finset.sum_congr rfl (fun x _ => show (1:ℤ) * x = x by simp)]
    exact ne_of_gt (lt_int_sum264 (fun x hx => by
      have hx' := hSR hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      omega) ⟨x₀, hx₀⟩)
