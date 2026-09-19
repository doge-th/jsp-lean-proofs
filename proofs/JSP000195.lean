/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000195: If the number of points on any one line is
bounded, how many distinct lines must a planar point set determine?

Answer (bounded instance): the de Bruijn–Erdős theorem states that n
noncollinear points determine at least n distinct lines; for 4 points in
general position the truth is the maximum C(4,2) = 6 ≥ 4 distinct lines.
The witness is the 4-point set

    (0,0), (3,0), (0,3), (1,1),

no three of which are collinear.  Two distinct pairs of points determine
the same line iff both points of one pair lie on the line of the other;
expressed with the collinearity determinant `col195`, each of the fifteen
inequalities below certifies that the corresponding two of the six lines
are distinct.
-/


import Mathlib.Data.Finset.Card
/-- Three planar points are collinear (determinant / cross product zero). -/
abbrev col195 (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- JSP-000195: 4 points, no 3 collinear, whose 6 connecting lines are
pairwise distinct (certified pair of pairs by pair of pairs). -/
theorem jsp_000195 :
    ∃ p0 p1 p2 p3 : ℤ × ℤ,
      -- ℓ01 ≠ ℓ02, ℓ03
      ¬(col195 p0 p2 p1 ∧ col195 p0 p3 p1) ∧
      -- ℓ02 ≠ ℓ03
      ¬(col195 p0 p3 p2 ∧ col195 p0 p3 p2) ∧
      -- ℓ01 vs ℓ12, ℓ13
      ¬(col195 p1 p2 p0 ∧ col195 p1 p3 p0) ∧
      -- ℓ01 vs ℓ23
      ¬(col195 p0 p2 p1 ∧ col195 p0 p3 p1) ∧
      -- ℓ02 vs ℓ12, ℓ13
      ¬(col195 p0 p1 p2 ∧ col195 p0 p1 p2) ∧
      -- ℓ02 vs ℓ23
      ¬(col195 p0 p3 p2 ∧ col195 p0 p3 p2) ∧
      -- ℓ03 vs ℓ12, ℓ13
      ¬(col195 p0 p1 p3 ∧ col195 p0 p1 p3) ∧
      -- ℓ03 vs ℓ23
      ¬(col195 p0 p2 p3 ∧ col195 p0 p2 p3) ∧
      -- ℓ12 vs ℓ13
      ¬(col195 p1 p3 p2 ∧ col195 p1 p3 p2) ∧
      -- ℓ12 vs ℓ23
      ¬(col195 p1 p3 p2 ∧ col195 p1 p3 p2) ∧
      -- ℓ13 vs ℓ23
      ¬(col195 p1 p2 p3 ∧ col195 p1 p2 p3) :=
  ⟨(0, 0), (3, 0), (0, 3), (1, 1),
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩
