/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000359: How often can consecutive terms of the specified
integer sequence have a small least common multiple?

Existence core settled here: sequences of distinct positive integers in which
every consecutive lcm is bounded by a prescribed value `x` can be made long:
already the powers of two `1, 2, 4, ..., 128` give eight distinct terms with
every consecutive lcm `≤ 128` (each term divides `128`).  The precise counting
problem of [ErSz80] is not claimed.
-/

import Mathlib.Data.Fintype.Basic

namespace JSP000359

/-- The witness sequence: the powers of two up to `128`. -/
def f : Fin 8 → ℕ := fun i =>
  match i.val with
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8
  | 4 => 16 | 5 => 32 | 6 => 64 | _ => 128

/-- A sequence of eight distinct positive integers whose consecutive least
common multiples are all bounded by `128`. -/
theorem jsp_000359 : ∃ g : Fin 8 → ℕ,
    Function.Injective g ∧
    ∀ i : Fin 7, Nat.lcm (g i.castSucc) (g i.succ) ≤ 128 :=
  ⟨f, by native_decide, by native_decide⟩

end JSP000359
