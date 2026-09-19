/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000076: How sparse can a set be if every two-coloring
represents every sufficiently large integer as a sum of distinct
same-colored elements?  Improve the growth bounds.

We formalize the defining property ("2-complete": under every
2-coloring of ℕ, every sufficiently large `n` is a finite sum of distinct
elements of `A` that all share one color) and establish the nonemptiness
benchmark: the full set `A = ℕ` is 2-complete, with every `n` represented
by the single-element sum `{n}`, which is monochromatic for a trivial
reason.  The actual problem — minimizing the growth of the counting
function of such an `A` — remains the deep part.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Basic

namespace JSP000076

/-- `A` is 2-complete: under every 2-coloring `c`, every sufficiently
large `n` is a sum of distinct elements of `A` all of one color. -/
def Complete2 (A : Set ℕ) : Prop :=
  ∀ c : ℕ → Bool, ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset ℕ,
    F.sum id = n ∧ (∀ x ∈ F, x ∈ A) ∧ ∃ b : Bool, ∀ x ∈ F, c x = b

/-- Benchmark instance: `ℕ` itself is 2-complete. -/
theorem univ_complete : Complete2 Set.univ := by
  intro c
  exact ⟨0, fun n _ => ⟨{n}, by simp, by simp, ⟨c n, by simp⟩⟩⟩

/-- Hence sets with the JSP-000076 property exist. -/
theorem exists_complete2 : ∃ A : Set ℕ, Complete2 A :=
  ⟨Set.univ, univ_complete⟩

end JSP000076
