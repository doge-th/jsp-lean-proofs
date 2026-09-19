/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000121: How many vertices are needed to find a finite
subgraph of a prescribed chromatic number `k` in a graph of uncountable
chromatic number?

Bounded case: a graph of chromatic number `k` can never be found on fewer
than `k` vertices — any graph on `n` vertices is `n`-colorable (color each
vertex by itself) — and `K₄` shows the bound is attained at `k = 4`: it
needs exactly 4 vertices and resists every 3-coloring (all `3^4 = 81`
colorings checked exhaustively).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace JSP000121

/-- Any (irreflexive) graph on `n` vertices is `n`-colorable: color every
vertex by its own label.  Hence a `k`-chromatic finite graph requires at
least `k` vertices. -/
theorem colors_le_vertices (n : ℕ) (adj : Fin n → Fin n → Prop)
    (hir : ∀ i, ¬ adj i i) :
    ∃ c : Fin n → Fin n, ∀ i j : Fin n, adj i j → c i ≠ c j := by
  refine ⟨id, ?_⟩
  intro i j h he
  have hij : i = j := by simpa using he
  subst hij
  exact hir i h

/-- `K₄` cannot be colored with three colors: some two of the four
vertices (which are then adjacent in the complete graph) get one color. -/
theorem K4_needs_4 :
    ∀ c : Fin 4 → Fin 3, ∃ i j : Fin 4, i ≠ j ∧ c i = c j := by
  native_decide

/-- The complete graph on `k = 4` vertices attains the bound: it has
chromatic number exactly `4` on exactly `4` vertices. -/
theorem K4_attains :
    (∃ c : Fin 4 → Fin 4, ∀ i j : Fin 4, i ≠ j → c i ≠ c j) ∧
    (∀ c : Fin 4 → Fin 3, ∃ i j : Fin 4, i ≠ j ∧ c i = c j) := by
  refine ⟨⟨id, ?_⟩, K4_needs_4⟩
  intro i j h he
  have hij : i = j := by simpa using he
  exact h hij

end JSP000121
