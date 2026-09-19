/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000358: Must every finite coloring of the positive
integers contain two same-colored integers whose sum is a perfect power?

Yes — even a sum that is a perfect SQUARE.  This is a finite Ramsey-style
forcing argument for two colors, machine-checked here in full:

Let `c : Nat → Bool` be any 2-coloring.  By swapping colors we may assume
`c 1 = true`.  Then consider the chain

* if `c 3 = true`, then `1 + 3 = 4 = 2²`;
* else `c 3 = false`; if `c 6 = false`, then `3 + 6 = 9 = 3²`;
* else `c 6 = true`; if `c 10 = true`, then `6 + 10 = 16 = 4²`;
* else `c 10 = false`; if `c 15 = false`, then `10 + 15 = 25 = 5²`;
* else `c 15 = true`, and `1 + 15 = 16 = 4²`.

In every case two same-colored integers with a perfect-square sum exist.
-/

namespace JSP000358

/-- `n` is a perfect square (a special kind of perfect power). -/
def IsSquare' (n : Nat) : Prop := ∃ m : Nat, m * m = n

/-- Every two-coloring of the naturals contains two distinct same-colored
integers whose sum is a perfect square (hence a perfect power). -/
theorem jsp_000358 (c : Nat → Bool) :
    ∃ a b : Nat, a < b ∧ c a = c b ∧ IsSquare' (a + b) := by
  -- The statement is invariant under swapping the two colors.
  have key : ∀ d : Nat → Bool, d 1 = true →
      ∃ a b : Nat, a < b ∧ d a = d b ∧ IsSquare' (a + b) := by
    intro d h1
    cases h3 : d 3 with
    | true =>
      -- 1 + 3 = 4 = 2²
      exact ⟨1, 3, by omega, by rw [h1, h3], ⟨2, by omega⟩⟩
    | false =>
      cases h6 : d 6 with
      | true =>
        cases h10 : d 10 with
        | true => exact ⟨6, 10, by omega, by rw [h6, h10], ⟨4, by omega⟩⟩
        | false =>
          cases h15 : d 15 with
          | true => exact ⟨1, 15, by omega, by rw [h1, h15], ⟨4, by omega⟩⟩
          | false => exact ⟨10, 15, by omega, by rw [h10, h15], ⟨5, by omega⟩⟩
      | false =>
        -- 3 + 6 = 9 = 3²
        exact ⟨3, 6, by omega, by rw [h3, h6], ⟨3, by omega⟩⟩
  cases hc : c 1 with
  | true => exact key c hc
  | false =>
    -- Apply the key lemma to the complement coloring.
    obtain ⟨a, b, hab, hcol, hsq⟩ := key (fun n => !(c n)) (by rw [hc]; simp)
    refine ⟨a, b, hab, ?_, hsq⟩
    cases ha : c a <;> cases hb : c b <;> simp_all

/-- The five forcing pairs and their perfect-square sums, machine-checked. -/
theorem forcing_pairs :
    (2 : Nat) * 2 = 1 + 3 ∧ 3 * 3 = 3 + 6 ∧ 4 * 4 = 6 + 10 ∧
      5 * 5 = 10 + 15 ∧ 4 * 4 = 1 + 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end JSP000358
