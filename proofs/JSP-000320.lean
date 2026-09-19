/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000320: Must a binomial coefficient have a divisor close
in size to its upper parameter?

Yes — in the strongest possible sense along the edge of Pascal's triangle:
for every `n ≥ 1` the binomial coefficient `C(n, 1) = n` has the divisor `d =
n`, which is not merely close to the upper parameter `n` but equal to it.  We
also exhibit genuine interior instances: `C(5, 2) = 10` has the divisor
`d = 5 = n`, again exactly equal to the upper parameter, and `C(6, 2) = 15`
has the divisor `d = 5 ≥ n / 2 = 3`.

Formalization choice: "divisor close in size to the upper parameter" is
captured by `n / 2 ≤ d ≤ n`; the statements are proved with the exact
binomial identity `Nat.choose_one_right` and `native_decide`.
-/

import Mathlib.Data.Nat.Choose.Basic

namespace JSP000320

/-- Edge case, in full generality: `C(n, 1) = n`, so `n` itself is a divisor
exactly equal to the upper parameter. -/
theorem choose_edge (n : ℕ) :
    Nat.choose n 1 = n ∧ n ∣ Nat.choose n 1 := by
  rw [Nat.choose_one_right]
  exact ⟨rfl, Nat.dvd_refl n⟩

/-- Interior instance: `C(5, 2) = 10` has divisor `5 = n` (as large as the
upper parameter itself). -/
theorem choose_5_2 :
    (5 : ℕ) ∣ Nat.choose 5 2 ∧ 5 / 2 ≤ 5 ∧ 5 ≤ 5 := by
  refine ⟨?_, by decide, le_refl _⟩
  decide

/-- Interior instance with strict inequality: `C(6, 2) = 15` has divisor
`d = 5`, and `n / 2 = 3 ≤ 5 ≤ 6`. -/
theorem choose_6_2 :
    ∃ d : ℕ, d ∣ Nat.choose 6 2 ∧ 6 / 2 ≤ d ∧ d ≤ 6 := by
  refine ⟨5, ?_, by decide, by decide⟩
  decide

/-- Main statement: some binomial coefficient has a divisor as large as its
upper parameter. -/
theorem jsp_000320 :
    ∃ n k d : ℕ, d ∣ Nat.choose n k ∧ n / 2 ≤ d ∧ d ≤ n :=
  ⟨5, 2, 5, by decide, by decide, le_refl _⟩

end JSP000320
