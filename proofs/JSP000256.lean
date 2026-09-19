/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000256: How small can the largest denominator be in
a representation of a given positive rational number by distinct unit
fractions?

Answer (bounded instance): for `q = 5/6` the minimum possible largest
denominator is `3`, attained by `5/6 = 1/2 + 1/3`; and `2` does not
suffice — a set of distinct denominators all `≤ 2` has scaled sum one of
`0, 30, 60, 90` (in units of `L = 60`), never `50 = 60 · 5/6`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-- JSP-000256: the least possible largest denominator for `5/6` is `3`. -/
theorem jsp_000256 :
    (∃ D : Finset ℕ, (∀ d ∈ D, 2 ≤ d ∧ d ≤ 3) ∧ (∑ d ∈ D, 60 / d) = 50) ∧
    (∀ D : Finset ℕ, (∀ d ∈ D, d ≤ 2) → (∑ d ∈ D, 60 / d) ≠ 50) := by
  refine ⟨⟨{2, 3}, by decide, by decide⟩, ?_⟩
  intro D hD
  have hT : D ⊆ insert 0 (insert 1 (insert 2 (∅ : Finset ℕ))) := by
    intro d hd
    have hx := hD d hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have e1 : (∑ d ∈ D, 60 / d) = ∑ d ∈ D, (if d ∈ D then 60 / d else 0) :=
    Finset.sum_congr rfl (fun d hd => by simp [hd])
  rw [e1, Finset.sum_subset hT (fun x _ hx => by simp [hx]),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by simp), Finset.sum_empty]
  by_cases h0 : (0:ℕ) ∈ D <;> by_cases h1 : (1:ℕ) ∈ D <;> by_cases h2 : (2:ℕ) ∈ D <;>
    simp [h0, h1, h2] <;> decide
