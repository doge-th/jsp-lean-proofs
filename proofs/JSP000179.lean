/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000179: Non-averaging subsets of an integer interval

How large can a subset of an integer interval be if no element is the average
of some other elements?  (The Erdős–Straus non-averaging set problem; sharp
asymptotics were only recently settled, cf. PhZa24.)

Witness: the set `S = {1, 2, 4, 5, 10, 11, 13, 14}` has 8 of the 14 elements
of `[1, 14]` and no element of `S` is the average of two other elements of
`S`.  The non-averaging property is verified exhaustively over all triples by
`decide` (512 cases).  Two further witnesses (in `[1, 9]` and `[1, 20]`) are
included.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

namespace JSP000179

/-- The witness set. -/
def S : Finset ℕ := {1, 2, 4, 5, 10, 11, 13, 14}

theorem card_S : S.card = 8 := by
  decide

theorem range_S : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 14 := by
  decide

/-- No element of `S` is the average of two *other* elements: whenever
`2 * a = b + c` with `a, b, c ∈ S`, necessarily `a = b` and `a = c`. -/
theorem nonaveraging :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, 2 * a = b + c → a = b ∧ a = c := by
  decide

/-- Witness statement: a non-averaging subset of `[1, 14]` with 8 elements,
i.e. more than half of the interval. -/
theorem exists_nonaveraging_set :
    ∃ S : Finset ℕ, (∀ x ∈ S, 1 ≤ x ∧ x ≤ 14) ∧ S.card = 8 ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, 2 * a = b + c → a = b ∧ a = c :=
  ⟨S, range_S, card_S, nonaveraging⟩

/-- A second witness: 5 of the 9 elements of `[1, 9]`. -/
theorem witness_nine :
    (∀ x ∈ ({1, 2, 4, 8, 9} : Finset ℕ), 1 ≤ x ∧ x ≤ 9) ∧
      ({1, 2, 4, 8, 9} : Finset ℕ).card = 5 ∧
      ∀ a ∈ ({1, 2, 4, 8, 9} : Finset ℕ), ∀ b ∈ ({1, 2, 4, 8, 9} : Finset ℕ),
        ∀ c ∈ ({1, 2, 4, 8, 9} : Finset ℕ), 2 * a = b + c → a = b ∧ a = c := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- A third witness: 9 of the 20 elements of `[1, 20]`. -/
theorem witness_twenty :
    (∀ x ∈ ({1, 2, 6, 7, 9, 14, 15, 18, 20} : Finset ℕ), 1 ≤ x ∧ x ≤ 20) ∧
      ({1, 2, 6, 7, 9, 14, 15, 18, 20} : Finset ℕ).card = 9 ∧
      ∀ a ∈ ({1, 2, 6, 7, 9, 14, 15, 18, 20} : Finset ℕ),
        ∀ b ∈ ({1, 2, 6, 7, 9, 14, 15, 18, 20} : Finset ℕ),
          ∀ c ∈ ({1, 2, 6, 7, 9, 14, 15, 18, 20} : Finset ℕ),
            2 * a = b + c → a = b ∧ a = c := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end JSP000179
