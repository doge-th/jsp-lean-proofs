/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000945: Is there an integer whose differences from
twice every permitted smaller square are all prime?

Witness: n = 13. The only s ≥ 1 with 2·s² < 13 are s = 1 and s = 2 (since
2·3² = 18 ≥ 13). The differences are 13 - 2 = 11 and 13 - 8 = 5, both prime.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000945

/-- Every `s ≥ 3` satisfies `s * s ≥ 9`. -/
lemma sq_ge_nine (s : ℕ) (hs : 3 ≤ s) : 9 ≤ s * s := Nat.mul_le_mul hs hs

/-- The existence statement of JSP-000945, answered affirmatively by the
witness `n = 13`: for every `s ≥ 1` with `2s² < 13` the difference
`13 - 2s²` is prime. -/
theorem jsp_000945 :
    ∃ n : ℕ, ∀ s : ℕ, 1 ≤ s → 2 * s * s < n → Nat.Prime (n - 2 * s * s) := by
  refine ⟨13, ?_⟩
  intro s hs hn
  have h3 : s < 3 := by
    rcases Nat.lt_or_ge s 3 with h | h
    · exact h
    · exfalso
      have h18 : 18 ≤ 2 * s * s := by
        have h2' : 2 * 9 ≤ 2 * (s * s) := Nat.mul_le_mul_left 2 (sq_ge_nine s h)
        rwa [← Nat.mul_assoc 2 s s] at h2'
      omega
  if h1 : s = 1 then
    subst h1
    exact (by native_decide : Nat.Prime (13 - 2 * 1 * 1))
  else
    have h2 : s = 2 := by omega
    subst h2
    exact (by native_decide : Nat.Prime (13 - 2 * 2 * 2))

/-- The two concrete prime differences of the witness `13`. -/
theorem witness_13 :
    Nat.Prime (13 - 2 * 1 * 1) ∧ Nat.Prime (13 - 2 * 2 * 2) := by
  constructor <;> native_decide

end JSP000945
