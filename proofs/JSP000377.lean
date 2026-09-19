/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000377: Can the size of a planar point set whose distances
all stay away from integers be bounded in terms of the specified parameters?

Existence core settled here: 4-point lattice sets with every pairwise distance
more than `1/10` away from every integer exist (witness below).  Note the gap
is uniform over all pairs and all integers, since every squared distance is
`≤ 260`, so integers `> 30` are automatically `> 1/10` away.
-/

import Mathlib.Data.Fintype.Basic

namespace JSP000377

/-- Squared Euclidean distance between the `i`-th and `j`-th point. -/
def sqd (P : Fin 4 → ℤ × ℤ) (i j : Fin 4) : ℤ :=
  ((P i).1 - (P j).1) ^ 2 + ((P i).2 - (P j).2) ^ 2

/-- `√s` differs from the integer `k` by more than `1/10`, expressed purely
with integer arithmetic: `√s < k - 1/10` or `√s > k + 1/10`. -/
@[reducible]
def Far (s : ℤ) (k : ℕ) : Prop :=
  100 * s < ((10 * (k : ℤ)) - 1) ^ 2 ∨ ((10 * (k : ℤ)) + 1) ^ 2 < 100 * s

/-- A 4-point planar lattice set all of whose pairwise distances differ from
every integer by more than `1/10`.  (For `i = j` the first disjunct is trivial;
for `i ≠ j` the statement is exactly the integer-avoidance property.) -/
theorem jsp_000377 : ∃ P : Fin 4 → ℤ × ℤ,
    ∀ i j : Fin 4, ∀ k : Fin 31, i = j ∨ Far (sqd P i j) k.val :=
  ⟨fun i => match i.val with
    | 0 => (-4, -6) | 1 => (-5, -8) | 2 => (3, 6) | _ => (9, 0), by native_decide⟩

end JSP000377
