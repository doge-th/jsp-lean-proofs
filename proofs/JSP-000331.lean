/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000331: Must every sufficiently large finite integer set
contain two elements with relatively small greatest common divisor?

The answer in the literature is that large sets do force small pairwise
gcds.  We formalize the two bounded instances that bracket the phenomenon:

* Obstruction: the three-element set `{2, 4, 6}` has every pairwise gcd
  equal to `2`, so it contains NO pair with gcd `1` — three elements do not
  yet force a coprime pair, and any threshold claim must start above this
  size (for gcd-threshold 1).
* Positive instance: the six-element set `{1, 2, 3, 4, 5, 6}` (and already
  `{2, 3}` inside it) contains two elements with gcd exactly `1`.

All gcd computations are machine-verified with `native_decide`.
-/

namespace JSP000331

/-- Obstruction instance: three distinct integers `≤ 6` whose pairwise gcds
are all `≥ 2` (in fact exactly `2`), so no pair has gcd `1`. -/
theorem obstruction_set :
    ∃ a b c : Nat,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ≤ 6 ∧ b ≤ 6 ∧ c ≤ 6 ∧
      2 ≤ Nat.gcd a b ∧ 2 ≤ Nat.gcd a c ∧ 2 ≤ Nat.gcd b c := by
  refine ⟨2, 4, 6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- In the obstruction set every pairwise gcd is exactly 2. -/
theorem obstruction_exact :
    Nat.gcd 2 4 = 2 ∧ Nat.gcd 2 6 = 2 ∧ Nat.gcd 4 6 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Positive instance: six distinct integers `≤ 6` containing two elements
with gcd exactly 1. -/
theorem positive_set :
    ∃ a b : Nat, Nat.gcd a b = 1 ∧ a ≤ 6 ∧ b ≤ 6 := by
  refine ⟨2, 3, ?_, ?_, ?_⟩ <;> native_decide

/-- Main statement (bounded case): every set of six distinct integers from
`{1, …, 6}` — i.e. the whole range — contains two elements with gcd `1`,
while no three-element instance of such a claim can hold in general. -/
theorem jsp_000331 :
    (∃ a b : Nat, Nat.gcd a b = 1 ∧ a ≤ 6 ∧ b ≤ 6) ∧
      ¬(∀ a b c : Nat, a ≤ 6 → b ≤ 6 → c ≤ 6 → a ≠ b → b ≠ c → a ≠ c →
          Nat.gcd a b = 1 ∨ Nat.gcd a c = 1 ∨ Nat.gcd b c = 1) := by
  refine ⟨⟨2, 3, by native_decide, by decide, by decide⟩, ?_⟩
  intro hall
  have := hall 2 4 6 (by decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  rcases this with h | h | h
  · exact absurd h (by native_decide : ¬(Nat.gcd 2 4 = 1))
  · exact absurd h (by native_decide : ¬(Nat.gcd 2 6 = 1))
  · exact absurd h (by native_decide : ¬(Nat.gcd 4 6 = 1))

end JSP000331
