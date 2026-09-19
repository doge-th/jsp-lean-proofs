/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000334: How many representations can an integer have as
a sum of powers of two, powers of three, and their products?

Existence core settled here: an integer can have several genuinely different
representations of this kind.  Witness: 36 = 4 + 32 = 9 + 27 = 12 + 24 = 18 + 18,
where every summand is of the form `2^i * 3^j` (pure powers of two, pure powers
of three, and products of the two).  The full problem (the exact maximum number
of representations and its asymptotics; cf. [TiWa88], [BaBe24]) is not claimed.
-/

import Mathlib.Data.Nat.Basic

namespace JSP000334

/-- `x` is a product of a power of two and a power of three (`2^i * 3^j`,
including the pure powers when `i = 0` or `j = 0`). -/
def IsTwoThreeSmooth (x : ℕ) : Prop := ∃ i j : ℕ, 2 ^ i * 3 ^ j = x

/-- There exists an integer with four distinct representations as a sum of
two numbers of the form `2^i * 3^j`. -/
theorem jsp_000334 : ∃ n : ℕ,
    ∃ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℕ,
      a₁ ≤ b₁ ∧ a₂ ≤ b₂ ∧ a₃ ≤ b₃ ∧ a₄ ≤ b₄ ∧
      (a₁, b₁) ≠ (a₂, b₂) ∧ (a₁, b₁) ≠ (a₃, b₃) ∧ (a₁, b₁) ≠ (a₄, b₄) ∧
      (a₂, b₂) ≠ (a₃, b₃) ∧ (a₂, b₂) ≠ (a₄, b₄) ∧ (a₃, b₃) ≠ (a₄, b₄) ∧
      n = a₁ + b₁ ∧ n = a₂ + b₂ ∧ n = a₃ + b₃ ∧ n = a₄ + b₄ ∧
      IsTwoThreeSmooth a₁ ∧ IsTwoThreeSmooth b₁ ∧
      IsTwoThreeSmooth a₂ ∧ IsTwoThreeSmooth b₂ ∧
      IsTwoThreeSmooth a₃ ∧ IsTwoThreeSmooth b₃ ∧
      IsTwoThreeSmooth a₄ ∧ IsTwoThreeSmooth b₄ := by
  refine ⟨36, 4, 32, 9, 27, 12, 24, 18, 18, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    rfl, rfl, rfl, rfl, ⟨2, 0, rfl⟩, ⟨5, 0, rfl⟩, ⟨0, 2, rfl⟩, ⟨0, 3, rfl⟩,
    ⟨2, 1, rfl⟩, ⟨3, 1, rfl⟩, ⟨1, 2, rfl⟩, ⟨1, 2, rfl⟩⟩

end JSP000334
