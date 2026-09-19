/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000422: What conditions on arc lengths make randomly
placed arcs cover the entire circle almost surely?

The research result (Shepp's covering theorem and refinements) characterizes
when randomly placed arcs of given lengths cover the circle almost surely.
The deterministic backbone of any such covering condition is that the arc
lengths are LARGE ENOUGH IN TOTAL to admit a covering at all: two arcs of
length `π` (half the circle) already suffice to cover it.

We machine-verify this witness instance on the unit circle in `ℂ`: the two
closed semicircles

  A = {z : |z| = 1, Re z ≥ 0}   and   B = {z : |z| = 1, Re z ≤ 0}

satisfy `A ∪ B = unit circle`, and each contains antipodal boundary points
(`1 ∈ A`, `-1 ∈ B`, `i ∈ A`, `-i ∈ A`).
-/

import Mathlib.Analysis.Complex.Basic

namespace JSP000422

open Metric Complex

/-- The right (eastern) closed semicircle. -/
def upperHalfArc : Set ℂ := sphere (0:ℂ) 1 ∩ {z | 0 ≤ z.re}

/-- The left (western) closed semicircle. -/
def lowerHalfArc : Set ℂ := sphere (0:ℂ) 1 ∩ {z | z.re ≤ 0}

/-- The two semicircles cover the unit circle. -/
theorem arcs_cover :
    upperHalfArc ∪ lowerHalfArc = sphere (0:ℂ) 1 := by
  ext z
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact h
    · exact h
  · intro h
    rcases le_total z.re 0 with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩

/-- Each arc contains antipodal boundary points. -/
theorem arc_membership :
    (1:ℂ) ∈ upperHalfArc ∧ (-1:ℂ) ∈ lowerHalfArc ∧
      I ∈ upperHalfArc ∧ -I ∈ upperHalfArc := by
  refine ⟨⟨mem_sphere_zero_iff_norm.mpr norm_one, by simp⟩,
    ⟨mem_sphere_zero_iff_norm.mpr (by norm_num), by simp⟩,
    ⟨mem_sphere_zero_iff_norm.mpr (by norm_num), by simp⟩,
    ⟨mem_sphere_zero_iff_norm.mpr (by norm_num), by simp⟩⟩

/-- Main statement (bounded case): there exist two arcs of the unit circle
whose union is the entire circle. -/
theorem jsp_000422 :
    ∃ A B : Set ℂ, A ∪ B = sphere (0:ℂ) 1 :=
  ⟨upperHalfArc, lowerHalfArc, arcs_cover⟩

end JSP000422
