/-
Helper module for JSP-000093: the K₆ witness coloring with no two
edge-disjoint monochromatic triangles.
-/

import JSP000093A

namespace JSP000093

/-- Two triangles are edge-disjoint when they share no (unordered) edge. -/
abbrev EdgeDisjoint {n : ℕ} (t₁ t₂ : Fin 3 → Fin n) : Prop :=
  ∀ p q r s : Fin 3,
    ¬ ((t₁ p = t₂ r ∧ t₁ q = t₂ s) ∨ (t₁ p = t₂ s ∧ t₁ q = t₂ r))

/-- The witness coloring of `K₆`: red edges are
01 02 03 04 12 13 15 23 45, all remaining edges blue. -/
def L6 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 3), (4, 5)]

def W6 (i j : Fin 6) : Bool :=
  (i.val, j.val) ∈ L6 || (j.val, i.val) ∈ L6

/-- The witness coloring does contain a monochromatic triangle
(namely `0,1,2`), so the R(3,3) bound is attained. -/
theorem witness_has_mono : ∃ t : Fin 3 → Fin 6, MonoTri W6 t := by
  native_decide

/-- Yet the witness coloring has no two edge-disjoint monochromatic
triangles: the guaranteed number of edge-disjoint monochromatic triangles
at `n = 6` is exactly `1`. -/
theorem witness_no_two_disjoint :
    ¬ ∃ t₁ t₂ : Fin 3 → Fin 6,
      MonoTri W6 t₁ ∧ MonoTri W6 t₂ ∧ EdgeDisjoint t₁ t₂ := by
  native_decide

end JSP000093
