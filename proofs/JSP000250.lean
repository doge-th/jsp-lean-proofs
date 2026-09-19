/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000250: Within the prescribed finite denominator
range `[2, 6]`, which initial denominators cannot occur in a
representation of one, and where is the smallest exception?

Answer: the only subset of `{2, 3, 4, 5, 6}` whose reciprocals sum to 1 is
`{2, 3, 6}` (scaled check: `30 + 20 + 10 = 60` with `L = 60`).  Hence the
denominators `2` and `3` do occur, while `4` and `5` cannot occur in any
such representation; the smallest initial denominator that is an exception
is `4`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases

/-- The scaled sum over a subset `D` of the window `{2, …, 6}` equals the
indicator linear form with weights `60/d`. -/
theorem linear250 (D : Finset ℕ) (hD : D ⊆ insert 2 (insert 3 (insert 4
    (insert 5 (insert 6 (∅ : Finset ℕ)))))) :
    (∑ d ∈ D, 60 / d) =
      30 * (if (2:ℕ) ∈ D then 1 else 0) + 20 * (if (3:ℕ) ∈ D then 1 else 0) +
      15 * (if (4:ℕ) ∈ D then 1 else 0) + 12 * (if (5:ℕ) ∈ D then 1 else 0) +
      10 * (if (6:ℕ) ∈ D then 1 else 0) := by
  have e1 : (∑ d ∈ D, 60 / d) = ∑ d ∈ D, (if d ∈ D then 60 / d else 0) :=
    Finset.sum_congr rfl (fun d hd => by simp [hd])
  rw [e1, Finset.sum_subset hD (fun x _ hx => by simp [hx]),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by simp), Finset.sum_empty]
  by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;>
    by_cases h5 : (5:ℕ) ∈ D <;> by_cases h6 : (6:ℕ) ∈ D <;>
    simp [h2, h3, h4, h5, h6] <;> decide

/-- JSP-000250: inside the range `[2, 6]` the representations of one use
exactly the denominators `{2, 3, 6}`; so `2` and `3` occur, `4` and `5`
never occur, and the smallest exception is `4`. -/
theorem jsp_000250 :
    (∀ D : Finset ℕ, (∀ d ∈ D, 2 ≤ d ∧ d ≤ 6) →
      ((∑ d ∈ D, 60 / d) = 60 ↔ D = {2, 3, 6})) ∧
    (4 ∉ ({2, 3, 6} : Finset ℕ)) ∧ (2 ∈ ({2, 3, 6} : Finset ℕ)) ∧
    (3 ∈ ({2, 3, 6} : Finset ℕ)) ∧ (5 ∉ ({2, 3, 6} : Finset ℕ)) := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro D hD
  constructor
  · intro hsum
    rw [linear250 D (fun d hd => by
      have hx := hD d hd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)] at hsum
    by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;>
      by_cases h5 : (5:ℕ) ∈ D <;> by_cases h6 : (6:ℕ) ∈ D <;>
      simp [h2, h3, h4, h5, h6] at hsum ⊢
    all_goals
      first
        | exact absurd hsum (by omega)
        | skip
    refine Finset.ext fun x => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      have hxb := hD x hx
      have hxv : x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
      rcases hxv with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hx h4
      · exact absurd hx h5
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact h2
      · exact h3
      · exact h6
  · intro hD2
    subst hD2
    decide
