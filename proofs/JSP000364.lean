/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000364: What proportion of an integer's divisors can be
paired with divisors of comparable size?

Existence core settled here: the proportion can be `1`.  For `n = 1536 = 2^9 * 3`
all twenty divisors split into ten disjoint pairs `(a, b)` with `a < b ≤ 2 * a`.
The general divisor-pairing estimates of [HaTe88] are not claimed.
-/

import Mathlib.NumberTheory.Divisors

namespace JSP000364

/-- A pair `(a, b)` of divisors of `n` of comparable size: `a < b ≤ 2 * a`. -/
@[reducible]
def ComparablePair (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∣ n ∧ p.2 ∣ n ∧ p.1 < p.2 ∧ p.2 ≤ 2 * p.1

/-- For `n = 1536` all twenty divisors are covered by ten disjoint pairs of
divisors of comparable size. -/
theorem jsp_000364 : ∃ n : ℕ, ∃ ps : List (ℕ × ℕ),
    (Nat.divisors n).card = 20 ∧ ps.length = 10 ∧
    ((ps.map Prod.fst) ++ (ps.map Prod.snd)).Nodup ∧
    ∀ p ∈ ps, ComparablePair n p := by
  refine ⟨1536, [(1, 2), (3, 4), (6, 8), (12, 16), (24, 32), (48, 64), (96, 128),
    (192, 256), (384, 512), (768, 1536)], ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> native_decide

end JSP000364
