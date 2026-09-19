/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000243: What is the shortest integer interval
containing distinct denominators whose reciprocals sum to one?

Answer: the interval `[2, 6]`, of length 4, with the representation
`1 = 1/2 + 1/3 + 1/6`.  Everything is scaled by the fixed denominator
`L = lcm(2,…,6) = 60`: a set D of denominators in an interval `[a, a+3]`
has reciprocal sum 1 iff `∑ d ∈ D, 60/d = 60`.

* No interval of length 3 or less works: if `a ≤ 2` then the denominators
  lie in `{2,3,4,5}` and the 16 subset sums `30b₂+20b₃+15b₄+12b₅` are
  never 60 (finite check); if `a ≥ 3` then the scaled sum is at most
  `60/3 + 60/4 + 60/5 + 60/6 = 20 + 15 + 12 + 10 = 57 < 60`.
* The interval `[2, 6]` works: `30 + 20 + 10 = 60`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-- Pointwise monotonicity of `Finset.sum` (not available in this Mathlib
build, so reproduced here). -/
theorem sum_le_sum_pt243 {S : Finset ℕ} {f g : ℕ → ℕ}
    (h : ∀ x ∈ S, f x ≤ g x) : S.sum f ≤ S.sum g := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
    have h1 : S.sum f ≤ S.sum g := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    have h2 : f a ≤ g a := h a (Finset.mem_insert_self a S)
    have e1 := Finset.sum_insert (ι := ℕ) (s := S) (a := a) (f := f) ha
    have e2 := Finset.sum_insert (ι := ℕ) (s := S) (a := a) (f := g) ha
    omega

/-- Subset monotonicity of `Finset.sum`. -/
theorem sum_le_sum_sub243 {S T : Finset ℕ} (f : ℕ → ℕ) (h : S ⊆ T) :
    S.sum f ≤ T.sum f := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
    have hx : a ∈ T := h (Finset.mem_insert_self a S)
    have hsub : S ⊆ T := fun x hx' => h (Finset.mem_insert_of_mem hx')
    by_cases haS : a ∈ S
    · rw [← Finset.insert_erase haS, Finset.sum_insert (by simp)]
      have h2 : (S.erase a).sum f ≤ T.sum f :=
        ih (fun x hx' => h (by simpa using (Finset.mem_erase.1 hx').2))
      rw [← Finset.insert_erase hx, Finset.sum_insert (by simp)]
      omega
    · rw [← Finset.insert_erase hx, Finset.sum_insert (by simp)]
      have h2 : S.sum f ≤ (T.erase a).sum f := ih (fun x hx' => h (by
        refine ⟨hsub hx', ?_⟩
        intro hxa
        exact haS (hxa ▸ hx')))
      omega

/-- JSP-000243: the shortest integer interval containing distinct
denominators (all ≥ 2) with reciprocals summing to 1 is `[2, 6]`. -/
theorem jsp_000243 :
    (∃ D : Finset ℕ, (∀ d ∈ D, 2 ≤ d ∧ d ≤ 6) ∧ (∑ d ∈ D, 60 / d) = 60) ∧
    (∀ a, 2 ≤ a → ∀ D : Finset ℕ, (∀ d ∈ D, a ≤ d ∧ d ≤ a + 3) →
      (∑ d ∈ D, 60 / d) ≠ 60) := by
  refine ⟨⟨{2, 3, 6}, by decide, by decide⟩, ?_⟩
  intro a ha D hD
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · -- a ≤ 2: denominators lie in {2,3,4,5}; finite check over the 16 subsets
    have hT : D ⊆ insert 2 (insert 3 (insert 4 (insert 5 (∅ : Finset ℕ)))) := by
      intro d hd
      have hx := hD d hd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have e1 : (∑ d ∈ D, 60 / d) = ∑ d ∈ D, (if d ∈ D then 60 / d else 0) :=
      Finset.sum_congr rfl (fun d hd => by simp [hd])
    rw [e1, Finset.sum_subset hT (fun x _ hx => by simp [hx]),
      Finset.sum_insert (by intro hx; simp at hx),
      Finset.sum_insert (by intro hx; simp at hx),
      Finset.sum_insert (by intro hx; simp at hx),
      Finset.sum_insert (by simp), Finset.sum_empty]
    by_cases h2 : (2:ℕ) ∈ D <;> by_cases h3 : (3:ℕ) ∈ D <;>
      by_cases h4 : (4:ℕ) ∈ D <;> by_cases h5 : (5:ℕ) ∈ D <;>
      simp [h2, h3, h4, h5] <;> decide
  · -- a ≥ 3: the scaled sum is bounded by 20 + 15 + 12 + 10 = 57 < 60
    have hT : D ⊆ insert a (insert (a+1) (insert (a+2) (insert (a+3)
        (∅ : Finset ℕ)))) := by
      intro d hd
      have hx := hD d hd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have e1 : (∑ d ∈ D, 60 / d) = ∑ d ∈ D, (if d ∈ D then 60 / d else 0) :=
      Finset.sum_congr rfl (fun d hd => by simp [hd])
    have b1 : 60 / a ≤ 20 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have b2 : 60 / (a + 1) ≤ 15 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have b3 : 60 / (a + 2) ≤ 12 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have b4 : 60 / (a + 3) ≤ 10 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have hle : (∑ d ∈ D, 60 / d) ≤ 57 := by
      rw [e1, Finset.sum_subset hT (fun x _ hx => by simp [hx]),
        Finset.sum_insert (by intro hx; simp at hx),
        Finset.sum_insert (by intro hx; simp at hx),
        Finset.sum_insert (by intro hx; simp at hx),
        Finset.sum_insert (by simp), Finset.sum_empty]
      split_ifs <;> omega
    exact ne_of_lt (by rw [hle]; omega)
