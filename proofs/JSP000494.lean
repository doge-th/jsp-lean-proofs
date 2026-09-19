/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000494 — Different multiplicity profiles of determined lines

How many different sets of line multiplicities can planar point
configurations determine?  Bounded instance for four points: the three
configurations of JSP-000493 have pairwise different multiplicity profiles

* `[4]` — four collinear points;
* `[2, 2, 2, 3]` — three collinear plus one off the line;
* `[2, 2, 2, 2, 2, 2]` — general position.

The profile of a configuration is the sorted list of point-counts of its
determined lines.
-/

namespace Mega5.JSP000494

/-- Normalized integer equation of the line through two distinct points. -/
def normLine (p q : ℤ × ℤ) : ℤ × ℤ × ℤ :=
  let a : ℤ := p.2 - q.2
  let b : ℤ := q.1 - p.1
  let g : ℕ := Nat.gcd a.natAbs b.natAbs
  let a' : ℤ := a / (g : ℤ)
  let b' : ℤ := b / (g : ℤ)
  let c' : ℤ := a' * p.1 + b' * p.2
  if a' < 0 ∨ (a' = 0 ∧ b' < 0) then (-(a'), -(b'), -(c')) else (a', b', c')

/-- All determined lines of a point set. -/
def determined (pts : List (ℤ × ℤ)) : List (ℤ × ℤ × ℤ) :=
  (List.range pts.length).flatMap
    (fun i => (List.range pts.length).filterMap
      (fun j => if i < j then some (normLine (pts.getD i 0) (pts.getD j 0))
                else none))

/-- Deduplicate a list. -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | a :: t => let r := dedup t; if r.contains a then r else a :: r

/-- Number of points on a line. -/
def multiplicity (line : ℤ × ℤ × ℤ) (pts : List (ℤ × ℤ)) : ℕ :=
  pts.countP (fun p => line.1 * p.1 + line.2.1 * p.2 = line.2.2)

/-- Insertion sort on naturals. -/
def isort : List ℕ → List ℕ
  | [] => []
  | a :: t => insertN a (isort t)
where insertN (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: t => if a ≤ b then a :: b :: t else b :: insertN a t

/-- The multiplicity profile of a configuration: sorted line multiplicities. -/
def profile (pts : List (ℤ × ℤ)) : List ℕ :=
  isort ((dedup (determined pts)).map (fun l => multiplicity l pts))

/-- The three profiles are as expected and pairwise different. -/
theorem three_distinct_profiles :
    profile [(0, 0), (1, 0), (2, 0), (3, 0)] = [4] ∧
    profile [(0, 0), (1, 0), (2, 0), (0, 1)] = [2, 2, 2, 3] ∧
    profile [(0, 0), (1, 0), (0, 1), (1, 1)] = [2, 2, 2, 2, 2, 2] := by
  native_decide

end Mega5.JSP000494
