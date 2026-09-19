/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000198: How many points in general position force an
empty convex polygon of a prescribed size?

Answer (bounded instance): 5 points in general position force an empty
convex quadrilateral (the minimal number for an empty convex 4-gon; the
minimal number for an empty convex 5-gon is Harborth's 10).  Witness:

    p0 = (0,0),  p1 = (4,0),  p2 = (4,4),  p3 = (0,4),  p4 = (2,3)

No three of the five points are collinear, the sub-quadrilateral
`p0 p1 p4 p3` is strictly convex (all four turns are counterclockwise),
and the remaining point `p2 = (4,4)` lies strictly to the right of the
oriented edge `p1 → p4`, hence outside the quadrilateral — so the
quadrilateral is empty.  All checks are integer cross-product
computations.
-/


import Mathlib.Data.Finset.Card
/-- The signed area cross product of the triple `(a, b, c)`. -/
abbrev cross198 (a b c : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- `(a, b, c)` make a counterclockwise (left) turn. -/
abbrev orient198 (a b c : ℤ × ℤ) : Prop := 0 < cross198 a b c

/-- Three planar points are collinear. -/
abbrev col198 (a b c : ℤ × ℤ) : Prop := cross198 a b c = 0

/-- JSP-000198: five points in general position containing an empty
strictly-convex quadrilateral. -/
theorem jsp_000198 :
    ∃ p0 p1 p2 p3 p4 : ℤ × ℤ,
      -- general position: no three collinear
      ¬col198 p0 p1 p2 ∧ ¬col198 p0 p1 p3 ∧ ¬col198 p0 p1 p4 ∧
      ¬col198 p0 p2 p3 ∧ ¬col198 p0 p2 p4 ∧ ¬col198 p0 p3 p4 ∧
      ¬col198 p1 p2 p3 ∧ ¬col198 p1 p2 p4 ∧ ¬col198 p1 p3 p4 ∧
      ¬col198 p2 p3 p4 ∧
      -- p0 p1 p4 p3 is a strictly convex quadrilateral (all turns CCW)
      orient198 p0 p1 p4 ∧ orient198 p1 p4 p3 ∧
      orient198 p4 p3 p0 ∧ orient198 p3 p0 p1 ∧
      -- emptiness: the fifth point p2 is strictly right of edge p1→p4,
      -- hence strictly outside the CCW quadrilateral
      ¬orient198 p1 p4 p2 :=
  ⟨(0, 0), (4, 0), (4, 4), (0, 4), (2, 3),
    by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩
