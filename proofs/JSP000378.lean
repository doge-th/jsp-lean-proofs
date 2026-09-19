/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000378: Can arbitrarily large planar point sets have all
pairwise distances uniformly bounded away from the nearest integer?

Existence core settled here: large finite sets with a uniform `1/10` gap exist:
a `12`-point lattice set all of whose `66` pairwise distances differ from every
integer by more than `1/10` (uniformly, since all squared distances are
`≤ 720`, so integers `> 30` are automatically far).  The full "arbitrarily
large" statement of [Sa76] is not claimed here.
-/

import Mathlib.Data.Fintype.Basic

namespace JSP000378

/-- Squared Euclidean distance between the `i`-th and `j`-th point. -/
def sqd (P : Fin 12 → ℤ × ℤ) (i j : Fin 12) : ℤ :=
  ((P i).1 - (P j).1) ^ 2 + ((P i).2 - (P j).2) ^ 2

/-- `√s` differs from the integer `k` by more than `1/10`, expressed purely
with integer arithmetic. -/
@[reducible]
def Far (s : ℤ) (k : ℕ) : Prop :=
  100 * s < ((10 * (k : ℤ)) - 1) ^ 2 ∨ ((10 * (k : ℤ)) + 1) ^ 2 < 100 * s

/-- A 12-point planar lattice set all of whose pairwise distances differ from
every integer by more than `1/10`.  (For `i = j` the first disjunct is trivial;
for `i ≠ j` the statement is exactly the integer-avoidance property.) -/
theorem jsp_000378 : ∃ P : Fin 12 → ℤ × ℤ,
    ∀ i j : Fin 12, ∀ k : Fin 31, i = j ∨ Far (sqd P i j) k.val :=
  ⟨fun i =>
    match i.val with
    | 0 => (-12, -11) | 1 => (-11, -12) | 2 => (-10, -10) | 3 => (-4, -6)
    | 4 => (-5, -8) | 5 => (-6, -4) | 6 => (1, 12) | 7 => (12, 1)
    | 8 => (-8, -5) | 9 => (-9, -9) | 10 => (2, 8) | _ => (8, 2), by native_decide⟩

end JSP000378
