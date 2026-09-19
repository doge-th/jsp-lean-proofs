/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000077: How fast must a set grow if every coloring
with more than two colors represents all sufficiently large integers as
sums of distinct same-colored elements?

We formalize the defining property for arbitrary (in particular more than
two) colors — under every coloring `c : ℕ → ℕ`, every sufficiently large
`n` is a finite sum of distinct elements of `A` all of one color — and
establish the nonemptiness benchmark: `A = ℕ` has the property via
single-element sums.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Basic

namespace JSP000077

/-- `A` is complete for arbitrary colorings: under every coloring
`c : ℕ → ℕ`, every sufficiently large `n` is a sum of distinct elements of
`A` all of one color. -/
def CompleteAny (A : Set ℕ) : Prop :=
  ∀ c : ℕ → ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset ℕ,
    F.sum id = n ∧ (∀ x ∈ F, x ∈ A) ∧ ∃ b : ℕ, ∀ x ∈ F, c x = b

/-- Benchmark instance: `ℕ` itself is complete for all colorings. -/
theorem univ_complete : CompleteAny Set.univ := by
  intro c
  exact ⟨0, fun n _ => ⟨{n}, by simp, by simp, ⟨c n, by simp⟩⟩⟩

/-- Hence sets with the JSP-000077 property exist. -/
theorem exists_complete_any : ∃ A : Set ℕ, CompleteAny A :=
  ⟨Set.univ, univ_complete⟩

end JSP000077
