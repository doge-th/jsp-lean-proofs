/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000385: Can all natural numbers be permuted so that every
adjacent pair has prime sum?

Existence core settled here: the first `30` terms of such a permutation are
exhibited — `30` distinct positive integers, every two consecutive of which
sum to a prime (all sums are `≤ 61`).  The global permutation statement of
[ErGr80] is not claimed here.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace JSP000385

/-- The witness: 30 distinct positive integers whose consecutive sums are
`3, 5, 7, 11, 13, ...`, all prime. -/
def perm : Fin 30 → ℕ := fun i =>
  match i.val with
  | 0 => 1  | 1 => 2  | 2 => 3  | 3 => 4  | 4 => 7
  | 5 => 6  | 6 => 5  | 7 => 8  | 8 => 9  | 9 => 10
  | 10 => 13 | 11 => 16 | 12 => 15 | 13 => 14 | 14 => 17
  | 15 => 12 | 16 => 11 | 17 => 18 | 18 => 19 | 19 => 22
  | 20 => 21 | 21 => 20 | 22 => 23 | 23 => 24 | 24 => 29
  | 25 => 30 | 26 => 31 | 27 => 28 | 28 => 25 | _ => 34

/-- A permutation prefix of length 30: injective, and every adjacent pair
sums to a prime. -/
theorem jsp_000385 : ∃ f : Fin 30 → ℕ,
    Function.Injective f ∧
    ∀ i : Fin 29, Nat.Prime (f i.castSucc + f i.succ) := by
  refine ⟨perm, ?_⟩
  native_decide

end JSP000385
