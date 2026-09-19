/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000093: How many edge-disjoint monochromatic triangles
are guaranteed in a two-coloring of the edges of a complete graph?

At `n = 6` the guaranteed number is exactly `1`:
  * every 2-coloring of the edges of `K₆` contains a monochromatic triangle
    (`R(3,3) ≤ 6`, verified exhaustively over the `2^15` colorings —
    see `JSP000093A`);
  * the exhibited coloring of `K₆` has monochromatic triangles but no two
    edge-disjoint ones (see `JSP000093B`);
  * the 5-cycle coloring of `K₅` has no monochromatic triangle at all,
    so nothing is guaranteed below `6` vertices.
-/

import JSP000093B

namespace JSP000093

/-- The 5-cycle coloring of `K₅` (cycle edges red, all other edges blue)
contains no monochromatic triangle. -/
def cyc5 (i j : Fin 5) : Bool :=
  (i.val + 1) % 5 = j.val || (j.val + 1) % 5 = i.val

theorem k5_no_mono : ∀ t : Fin 3 → Fin 5, ¬ MonoTri cyc5 t := by
  native_decide

/-- Combined shape of the `n = 6` answer: at least one monochromatic
triangle always exists, and one is sometimes best possible. -/
theorem min_edge_disjoint_mono_triangles_K6 :
    (∀ c : Fin 6 → Fin 6 → Bool,
      (∀ i j : Fin 6, c i j = c j i) → ∃ t : Fin 3 → Fin 6, MonoTri c t) ∧
    (∃ c : Fin 6 → Fin 6 → Bool,
      (∃ t : Fin 3 → Fin 6, MonoTri c t) ∧
        ¬ ∃ t₁ t₂ : Fin 3 → Fin 6,
          MonoTri c t₁ ∧ MonoTri c t₂ ∧ EdgeDisjoint t₁ t₂) :=
  ⟨r33_le_6, ⟨W6, witness_has_mono, witness_no_two_disjoint⟩⟩

end JSP000093
