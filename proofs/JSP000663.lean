/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000663: A square-root-scale set covered by the two-term sumset of a much smaller set

Erdős and Newman (1977) asked whether an integer set of "square-root scale"
can be covered by the two-term sumset of a smaller set; Alon, Balogh,
Samotij and Solymosi (2009) studied the complementary question of small
bases.  Here we give an explicit witness of the covering phenomenon:

Take `N = 10000` and the square-root-scale set `A = [0, 99]`, so `|A| = 100
= √N` and `A ⊆ [0, N)`.  The set

  B = [0, 13] ∪ {26, 39, 52, 65, 78, 91}

has `|B| = 20 < 100 = |A|`, and every `n ∈ A` decomposes as

  n = 13·(n/13) + (n mod 13)  with  13·(n/13) ∈ B,  n mod 13 ∈ [0, 13] ⊆ B,

so `A ⊆ B + B`: an integer set of square-root-scale size is covered by the
two-term sumset of a much smaller set.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.IntervalCases

namespace JSP000663

/-- The smaller covering set. -/
def B : Finset Nat := Finset.range 14 ∪ {26, 39, 52, 65, 78, 91}

/-- The square-root-scale covered set. -/
def A : Finset Nat := Finset.range 100

/-- Every `n ∈ A` is a sum of two elements of `B`. -/
theorem coverage : ∀ n ∈ A, ∃ b1 ∈ B, ∃ b2 ∈ B, n = b1 + b2 := by
  intro n hn
  simp only [A, Finset.mem_range] at hn
  have hmod : n % 13 < 13 := Nat.mod_lt n (by omega)
  have hq : n / 13 ≤ 7 := by omega
  refine ⟨13 * (n / 13), ?_, n % 13, ?_, by omega⟩
  · simp only [B, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    interval_cases n / 13 <;> simp <;> omega
  · simp only [B, Finset.mem_union, Finset.mem_range]
    omega

/-- The main witness statement (the last conjunct is `A ⊆ B + B` spelled
out as a covering property). -/
theorem jsp_000663 :
    ∃ (N : Nat) (A B : Finset Nat),
      N = 10000 ∧
      (∀ a ∈ A, a < N) ∧
      A.card = Nat.sqrt N ∧
      (∀ a ∈ A, ∃ b1 ∈ B, ∃ b2 ∈ B, a = b1 + b2) ∧
      B.card < A.card := by
  refine ⟨10000, A, B, rfl, ?_, ?_, coverage, ?_⟩
  · intro a ha
    simp only [A, Finset.mem_range] at ha
    omega
  · simp only [A, Finset.card_range]
    decide
  · have h1 : A.card = 100 := by simp [A, Finset.card_range]
    have h2 : B.card = 20 := by decide
    omega

end JSP000663
