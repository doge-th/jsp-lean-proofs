/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000514 — Triangles dissected into congruent triangles

Which triangles can be dissected into congruent triangles only when their
number is a square?  Bounded instance showcasing the square-number condition
with a non-right triangle: the scalene, non-right triangle with vertices
`(0,0), (4,0), (1,3)` is dissected — by the classical midpoint construction —
into `N = 4 = 2^2` congruent triangles, each similar to the original.

Coordinates are doubled (all integer) to keep arithmetic in `ℤ`; this scales
all squared lengths by a common factor and does not affect any of the
incidences.  We verify
* the four pieces are mutually congruent (equal sorted side-squared lists),
* each piece is similar to the original triangle (its side-squared list
  multiplied by the square of the similarity factor `2` equals the
  original's),
* every vertex of every piece lies inside the original triangle,
* the piece areas sum to the area of the original (a dissection certificate),
* the original triangle is not right-angled, and `4 = 2^2` is a square.
-/

namespace Mega5.JSP000514

/-- Squared distance in integer coordinates. -/
abbrev ssq (p q : ℤ × ℤ) : ℤ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Insertion into a sorted list. -/
def insQ (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: t => if x ≤ y then x :: y :: t else y :: insQ x t

/-- Insertion sort. -/
def isortQ : List ℤ → List ℤ
  | [] => []
  | x :: t => insQ x (isortQ t)

/-- Sorted list of squared side lengths of the triangle with given vertices. -/
abbrev sides (t : List (ℤ × ℤ)) : List ℤ :=
  isortQ [ssq (t.getD 0 (0, 0)) (t.getD 1 (0, 0)),
          ssq (t.getD 1 (0, 0)) (t.getD 2 (0, 0)),
          ssq (t.getD 0 (0, 0)) (t.getD 2 (0, 0))]

/-- Signed double area of a triangle. -/
abbrev darea (a b c : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Point `p` inside (or on the boundary of) triangle `abc`. -/
abbrev inTri (a b c p : ℤ × ℤ) : Prop :=
  (darea a b c ≥ 0 ∧
    darea a b p ≥ 0 ∧ darea b c p ≥ 0 ∧ darea c a p ≥ 0) ∨
  (darea a b c ≤ 0 ∧
    darea a b p ≤ 0 ∧ darea b c p ≤ 0 ∧ darea c a p ≤ 0)

/-- The original non-right triangle (doubled coordinates). -/
abbrev O : ℤ × ℤ := (0, 0)
abbrev B : ℤ × ℤ := (8, 0)
abbrev C : ℤ × ℤ := (2, 6)

/-- The midpoints of the sides (doubled coordinates). -/
abbrev M1 : ℤ × ℤ := (4, 0)
abbrev M2 : ℤ × ℤ := (5, 3)
abbrev M3 : ℤ × ℤ := (1, 3)

/-- The four pieces of the midpoint dissection, as vertex lists. -/
abbrev T1 : List (ℤ × ℤ) := [O, M1, M3]
abbrev T2 : List (ℤ × ℤ) := [M1, B, M2]
abbrev T3 : List (ℤ × ℤ) := [M3, M2, C]
abbrev T4 : List (ℤ × ℤ) := [M1, M2, M3]

/-- All pieces together. -/
abbrev pieces : List (List (ℤ × ℤ)) := [T1, T2, T3, T4]

/-- The number of pieces is a square. -/
theorem four_is_square : (4 : ℤ) = 2 ^ 2 := rfl

/-- The original triangle is scalene and not right-angled: its squared sides
    are `40, 64, 72` and no two sum to the third. -/
theorem not_right :
    sides [O, B, C] = [40, 64, 72] ∧
    (40 + 64 ≠ 72 ∧ 40 + 72 ≠ 64 ∧ 64 + 72 ≠ 40) := by
  native_decide

/-- The four pieces are mutually congruent. -/
theorem congruent_pieces :
    sides T1 = sides T2 ∧ sides T1 = sides T3 ∧ sides T1 = sides T4 := by
  native_decide

/-- Each piece is similar to the original triangle: squared sides multiplied
    by `4` (the square of the similarity factor `2`) give the original's. -/
theorem similar_pieces :
    (sides T1).map (· * 4) = sides [O, B, C] ∧
    (sides T2).map (· * 4) = sides [O, B, C] ∧
    (sides T3).map (· * 4) = sides [O, B, C] ∧
    (sides T4).map (· * 4) = sides [O, B, C] := by
  native_decide

/-- Every vertex of every piece lies inside the original triangle. -/
theorem pieces_inside :
    ∀ t ∈ pieces, ∀ p ∈ t, inTri O B C p := by
  native_decide

/-- The areas of the four pieces sum to the area of the original (doubled
    signed areas: `48` for the original, `12` for each piece). -/
theorem area_certificate :
    darea O B C = 48 ∧
    darea (T1.getD 0 O) (T1.getD 1 O) (T1.getD 2 O) = 12 ∧
    darea (T2.getD 0 O) (T2.getD 1 O) (T2.getD 2 O) = 12 ∧
    darea (T3.getD 0 O) (T3.getD 1 O) (T3.getD 2 O) = 12 ∧
    darea (T4.getD 0 O) (T4.getD 1 O) (T4.getD 2 O) = 12 ∧
    (12 + 12 + 12 + 12 : ℤ) = 48 := by
  native_decide

end Mega5.JSP000514
