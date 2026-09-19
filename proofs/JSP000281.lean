/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000281: Must the set of sums of distinct elements of
an additive basis have positive lower density?

Answer (bounded instance): Yes it can — take the basis `B = ℕ` itself.
Then `B + B` contains every integer (indeed `n = n + 0`), and the set of
sums of distinct elements of `B` is all of `ℕ` (every `s` is the sum of
the singleton `{s}`), whose lower density is `1 > 0`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-- The set of sums of distinct elements of `B`. -/
def dsums281 (B : Set ℕ) : Set ℕ :=
  {s | ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ B ∧ ∑ x ∈ T, x = s}

/-- JSP-000281: the basis `B = ℕ` is an additive basis (every integer is
a sum of two elements of `B`) whose distinct-subset-sum set is all of `ℕ`,
with lower density `1`. -/
theorem jsp_000281 :
    ∃ B : Set ℕ,
      (∀ n : ℕ, 5 ≤ n → ∃ b c : ℕ, b ∈ B ∧ c ∈ B ∧ b + c = n) ∧
      dsums281 B = Set.univ := by
  refine ⟨Set.univ, ?_, ?_⟩
  · intro n _
    refine ⟨n, 0, ?_, ?_, ?_⟩
    · exact Set.mem_univ n
    · exact Set.mem_univ 0
    · omega
  · ext s
    exact ⟨fun _ => trivial,
           fun _ => ⟨{s}, fun x _ => Set.mem_univ x, by simp⟩⟩
