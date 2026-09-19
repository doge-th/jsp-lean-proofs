/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000248: Which positive integers can be the largest
denominator in a representation of one by distinct unit fractions
(denominators ≥ 2)?

Answer (bounded instance): 6 and 12 are achievable —
`1 = 1/2 + 1/3 + 1/6` and `1 = 1/2 + 1/4 + 1/6 + 1/12` — while
`2, 3, 4, 5, 7` are not: for each of these n a direct subset check below
shows no set of distinct denominators with maximum exactly n sums to 1.
All sums are scaled by `L = lcm(2,…,12) = 27720` (so `∑ 1/d = 1` becomes
`∑ 27720/d = 27720`, with `27720/d` integral for every `d ≤ 12`).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-- The scaled sum over a subset `D` of the window `{2, …, 7}` equals the
indicator linear form with weights `27720/d`. -/
theorem linear248 (D : Finset ℕ) (hD : D ⊆ insert 2 (insert 3 (insert 4
    (insert 5 (insert 6 (insert 7 (∅ : Finset ℕ))))))) :
    (∑ d ∈ D, 27720 / d) =
      13860 * (if (2:ℕ) ∈ D then 1 else 0) + 9240 * (if (3:ℕ) ∈ D then 1 else 0) +
      6930 * (if (4:ℕ) ∈ D then 1 else 0) + 5544 * (if (5:ℕ) ∈ D then 1 else 0) +
      4620 * (if (6:ℕ) ∈ D then 1 else 0) + 3960 * (if (7:ℕ) ∈ D then 1 else 0) := by
  have e1 : (∑ d ∈ D, 27720 / d) = ∑ d ∈ D, (if d ∈ D then 27720 / d else 0) :=
    Finset.sum_congr rfl (fun d hd => by simp [hd])
  rw [e1, Finset.sum_subset hD (fun x _ hx => by simp [hx]),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by intro hx; simp at hx),
    Finset.sum_insert (by simp), Finset.sum_empty]
  by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;>
    by_cases h5 : (5:ℕ) ∈ D <;> by_cases h6 : (6:ℕ) ∈ D <;> by_cases h7 : (7:ℕ) ∈ D <;>
    simp [h2, h3, h4, h5, h6, h7] <;> decide

/-- JSP-000248: 6 and 12 occur as the largest denominator; 2, 3, 4, 5, 7
do not. -/
theorem jsp_000248 :
    (∃ D : Finset ℕ, 6 ∈ D ∧ (∀ d ∈ D, 2 ≤ d ∧ d ≤ 6) ∧
      (∑ d ∈ D, 27720 / d) = 27720) ∧
    (∃ D : Finset ℕ, 12 ∈ D ∧ (∀ d ∈ D, 2 ≤ d ∧ d ≤ 12) ∧
      (∑ d ∈ D, 27720 / d) = 27720) ∧
    (∀ D : Finset ℕ, 2 ∈ D → (∀ d ∈ D, 2 ≤ d ∧ d ≤ 2) →
      (∑ d ∈ D, 27720 / d) ≠ 27720) ∧
    (∀ D : Finset ℕ, 3 ∈ D → (∀ d ∈ D, 2 ≤ d ∧ d ≤ 3) →
      (∑ d ∈ D, 27720 / d) ≠ 27720) ∧
    (∀ D : Finset ℕ, 4 ∈ D → (∀ d ∈ D, 2 ≤ d ∧ d ≤ 4) →
      (∑ d ∈ D, 27720 / d) ≠ 27720) ∧
    (∀ D : Finset ℕ, 5 ∈ D → (∀ d ∈ D, 2 ≤ d ∧ d ≤ 5) →
      (∑ d ∈ D, 27720 / d) ≠ 27720) ∧
    (∀ D : Finset ℕ, 7 ∈ D → (∀ d ∈ D, 2 ≤ d ∧ d ≤ 7) →
      (∑ d ∈ D, 27720 / d) ≠ 27720) := by
  refine ⟨⟨{2, 3, 6}, by decide, by decide, by decide⟩,
    ⟨{2, 4, 6, 12}, by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro D hi hD
    rw [linear248 D (fun d hd => by
      have hx := hD d hd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)]
  · have hno : ∀ d : ℕ, 3 ≤ d → (d:ℕ) ∈ D → False := fun d hd hx =>
      absurd (hD d hx).2 (by omega)
    by_cases h3 : (3:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;> by_cases h5 : (5:ℕ) ∈ D <;>
      by_cases h6 : (6:ℕ) ∈ D <;> by_cases h7 : (7:ℕ) ∈ D <;>
      simp [hi, h3, h4, h5, h6, h7] <;>
      first
        | exact absurd h3 (hno 3 (by omega))
        | exact absurd h4 (hno 4 (by omega))
        | exact absurd h5 (hno 5 (by omega))
        | exact absurd h6 (hno 6 (by omega))
        | exact absurd h7 (hno 7 (by omega))
        | decide
  · have hno : ∀ d : ℕ, 4 ≤ d → (d:ℕ) ∈ D → False := fun d hd hx =>
      absurd (hD d hx).2 (by omega)
    by_cases h2 : (2:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;> by_cases h5 : (5:ℕ) ∈ D <;>
      by_cases h6 : (6:ℕ) ∈ D <;> by_cases h7 : (7:ℕ) ∈ D <;>
      simp [hi, h2, h4, h5, h6, h7] <;>
      first
        | exact absurd h4 (hno 4 (by omega))
        | exact absurd h5 (hno 5 (by omega))
        | exact absurd h6 (hno 6 (by omega))
        | exact absurd h7 (hno 7 (by omega))
        | decide
  · have hno : ∀ d : ℕ, 5 ≤ d → (d:ℕ) ∈ D → False := fun d hd hx =>
      absurd (hD d hx).2 (by omega)
    by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;> by_cases h5 : (5:ℕ) ∈ D <;>
      by_cases h6 : (6:ℕ) ∈ D <;> by_cases h7 : (7:ℕ) ∈ D <;>
      simp [hi, h2, h3, h5, h6, h7] <;>
      first
        | exact absurd h5 (hno 5 (by omega))
        | exact absurd h6 (hno 6 (by omega))
        | exact absurd h7 (hno 7 (by omega))
        | decide
  · have hno : ∀ d : ℕ, 6 ≤ d → (d:ℕ) ∈ D → False := fun d hd hx =>
      absurd (hD d hx).2 (by omega)
    by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;>
      by_cases h6 : (6:ℕ) ∈ D <;> by_cases h7 : (7:ℕ) ∈ D <;>
      simp [hi, h2, h3, h4, h6, h7] <;>
      first
        | exact absurd h6 (hno 6 (by omega))
        | exact absurd h7 (hno 7 (by omega))
        | decide
  · by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;> by_cases h4 : (4:ℕ) ∈ D <;>
      by_cases h5 : (5:ℕ) ∈ D <;> by_cases h6 : (6:ℕ) ∈ D <;>
      simp [hi, h2, h3, h4, h5, h6] <;> decide
