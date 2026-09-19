/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000194: How many ordinary lines, each containing
exactly two of the points, must a finite noncollinear planar point set
determine?

Answer (bounded instance): for 4 points the Dirac–Motzkin lower bound n/2
is far from sharp — a noncollinear 4-point set in general position
determines all 6 of its connecting lines as ordinary lines, and 6 ≥ 4/2.
The witness is the 4-point set

    (0,0), (3,0), (0,3), (1,1)

no three of which are collinear; consequently each of the six pairs spans
a line containing exactly those two of the given points.  Collinearity of
`p, q, r` is encoded by the vanishing of the cross product
`(q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)`, and all checks
are integer computations.
-/


import Mathlib.Data.Finset.Card
/-- Three planar points are collinear (determinant / cross product zero). -/
abbrev col194 (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- JSP-000194: a noncollinear 4-point set all of whose 6 connecting lines
are ordinary. -/
theorem jsp_000194 :
    ∃ p0 p1 p2 p3 : ℤ × ℤ,
      ¬col194 p0 p1 p2 ∧ ¬col194 p0 p1 p3 ∧ ¬col194 p0 p2 p3 ∧
      ¬col194 p1 p2 p3 ∧
      -- line p0p1 contains neither p2 nor p3
      ¬col194 p0 p2 p1 ∧ ¬col194 p0 p3 p1 ∧
      -- line p0p2 contains neither p1 nor p3
      ¬col194 p0 p1 p2 ∧ ¬col194 p0 p3 p2 ∧
      -- line p0p3 contains neither p1 nor p2
      ¬col194 p0 p1 p3 ∧ ¬col194 p0 p2 p3 ∧
      -- line p1p2 contains neither p0 nor p3
      ¬col194 p1 p0 p2 ∧ ¬col194 p1 p3 p2 ∧
      -- line p1p3 contains neither p0 nor p2
      ¬col194 p1 p0 p3 ∧ ¬col194 p1 p2 p3 ∧
      -- line p2p3 contains neither p0 nor p1
      ¬col194 p2 p0 p3 ∧ ¬col194 p2 p1 p3 :=
  ⟨(0, 0), (3, 0), (0, 3), (1, 1),
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩
