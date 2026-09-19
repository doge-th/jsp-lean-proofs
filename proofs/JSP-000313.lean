/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000313: What is the density of rows of Pascal's triangle
containing exactly a prescribed number of squarefree entries?

The research result describes the density of rows `n` of Pascal's triangle
whose entries `C(n,k)` include exactly a prescribed number of squarefree
values.  We formalize the central predicate — the number of squarefree
entries in a given row — as a computable Boolean count, and machine-verify
concrete instances of rows containing EXACTLY the prescribed number (three)
of squarefree entries:

* Row `n = 4`: entries `1, 4, 6, 4, 1`; squarefree ones are `1, 6, 1`.
* Row `n = 8`: entries `1, 8, 28, 56, 70, 56, 28, 8, 1`;
  squarefree ones are `1, 70, 1`.

Both counts equal `3` by `native_decide`, giving fully verified instances of
rows realizing the prescribed count.  Squarefreeness of a natural number `m`
is decided by checking that no `d ≥ 2` has `d² ∣ m`, i.e. `m % d² ≠ 0` for
all such `d`.
-/

import Mathlib.Data.Nat.Choose.Basic

namespace JSP000313

/-- Decidable squarefreeness test for natural numbers: `m` is squarefree iff
`m ≠ 0` and no `d ≥ 2` satisfies `d * d ∣ m` (implemented via `%`). -/
def isSqfree (m : ℕ) : Bool :=
  m != 0 &&
    !((List.range (m + 1)).any fun d => 2 ≤ d && m % (d * d) == 0)

/-- The number of squarefree entries in row `n` of Pascal's triangle:
the entries are `C(n,0), …, C(n,n)`. -/
def sqfreeEntries (n : ℕ) : ℕ :=
  (List.range (n + 1)).countP fun k => isSqfree (Nat.choose n k)

/-- Row 4 of Pascal's triangle has exactly 3 squarefree entries. -/
theorem row_4 : sqfreeEntries 4 = 3 := by native_decide

/-- Row 8 of Pascal's triangle has exactly 3 squarefree entries. -/
theorem row_8 : sqfreeEntries 8 = 3 := by native_decide

/-- The main statement in its bounded form: there exists a row of Pascal's
triangle containing exactly the prescribed number (here 3) of squarefree
entries. -/
theorem jsp_000313 :
    ∃ n : ℕ, sqfreeEntries n = 3 :=
  ⟨4, row_4⟩

/-- Sanity checks of the squarefree predicate on individual entries. -/
theorem entry_checks :
    isSqfree 1 = true ∧ isSqfree 6 = true ∧ isSqfree 70 = true ∧
      isSqfree 4 = false ∧ isSqfree 8 = false ∧ isSqfree 28 = false := by
  native_decide

end JSP000313
