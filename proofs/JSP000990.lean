/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000990: Can long arithmetic progressions in dense
integer sets be required to have common difference in another specified
set's difference set?

We formalize the ingredients — positive lower density (for a boolean
indicator of the set), the difference set `Δ(B) = {b₁ - b₂}` — and give an
affirmative instance: there exist a dense `A` and a nonempty `B` (namely
`A = ℕ`, `B = {0, 1}`, whose difference set contains `1`) such that `A`
contains arithmetic progressions of every length with common difference
in `Δ(B)`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Basic

namespace JSP000990

/-- `A` (given by its indicator function) has lower density at least
`1/2` on every initial segment. -/
def Dense (A : ℕ → Bool) : Prop :=
  ∀ N : ℕ, N / 2 ≤ ((Finset.range N).filter (fun x => A x = true)).card

/-- The difference set `Δ(B) = {b₁ - b₂ : b₁, b₂ ∈ B}`. -/
def DeltaSet (B : Set ℤ) : Set ℤ := {d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}

/-- Affirmative instance: a dense set with progressions of every length
whose common difference lies in a prescribed nonempty set's difference
set. -/
theorem jsp_000990_instance :
    ∃ A : ℕ → Bool, Dense A ∧ ∃ B : Set ℤ, B.Nonempty ∧
      ∀ k : ℕ, 0 < k → ∃ a d : ℕ, 0 < d ∧ (d : ℤ) ∈ DeltaSet B ∧
        ∀ i : ℕ, i < k → A (a + i * d) = true := by
  refine ⟨fun _ => true, fun N => ?_, {0, 1}, ⟨1, by simp⟩, fun k _ => ?_⟩
  · have h : ((Finset.range N).filter (fun _ => (true : Bool) = true)).card
        = (Finset.range N).card := by simp
    rw [h, Finset.card_range]
    exact Nat.div_le_self N 2
  · exact ⟨0, 1, Nat.one_pos, ⟨1, by simp, 0, by simp, rfl⟩,
      fun _ _ => rfl⟩

end JSP000990
