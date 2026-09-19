/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000176: How many edges can a graph have if it contains
no regular subgraph of a prescribed degree?

Answer (bounded instance): for prescribed degree 2, a graph on 4 vertices
can have 3 edges without containing any 2-regular subgraph — the 3-edge
star `K_{1,3}`.  Every nonempty subgraph F of the star fails to be
2-regular: if `(0, b)` is an edge of F with `b ∈ {1, 2, 3}`, then no edge
of F has first coordinate b (the star's tails are all 0 and `b ≠ 0`), and
the only possible edge of F incident to b is `(0, b)` itself; hence
`deg_F b ≤ 1 ≠ 2`.
-/

import Mathlib.Data.Finset.Card

/-- Vertex degrees of an edge set (no loops occur in our example, so
counting both coordinates is correct). -/
def deg176 (F : Finset (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (F.filter (fun e => e.1 = v)).card + (F.filter (fun e => e.2 = v)).card

/-- The 3-edge star `K_{1,3}` on vertices `{0, 1, 2, 3}`. -/
def star176 : Finset (ℕ × ℕ) := {(0, 1), (0, 2), (0, 3)}

/-- JSP-000176: the star has 3 edges and contains no 2-regular subgraph. -/
theorem jsp_000176 :
    ∃ E : Finset (ℕ × ℕ), E.card = 3 ∧
      ∀ F, F ⊆ E → F.Nonempty → ∃ v, deg176 F v ≠ 2 := by
  refine ⟨star176, by native_decide, ?_⟩
  intro F hF ⟨e, he⟩
  obtain ⟨a, b⟩ := e
  have hestar : (a, b) ∈ star176 := hF he
  simp only [star176, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hestar
  have hb : b = 1 ∨ b = 2 ∨ b = 3 := by
    rcases hestar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  -- every edge of F whose second coordinate is b must be `(0, b)`
  have hsnd : F.filter (fun e => e.2 = b) ⊆ {(0, b)} := by
    intro x hx
    obtain ⟨hxF, hxb⟩ := Finset.mem_filter.1 hx
    obtain ⟨u, w⟩ := x
    have hxstar : (u, w) ∈ star176 := hF hxF
    simp only [star176, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hxstar
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    have hw : w = b := by simpa using hxb
    rcases hxstar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  have h1 : (F.filter (fun e => e.2 = b)).card ≤ 1 := by
    have := Finset.card_le_card hsnd
    simpa using this
  -- no edge of F has first coordinate b (the star's tails are all 0, b ≠ 0)
  have h2 : (F.filter (fun e => e.1 = b)).card = 0 := by
    have hsub : F.filter (fun e => e.1 = b) ⊆ (∅ : Finset (ℕ × ℕ)) := by
      intro x hx
      obtain ⟨hxF, hxb⟩ := Finset.mem_filter.1 hx
      obtain ⟨u, w⟩ := x
      have hxstar : (u, w) ∈ star176 := hF hxF
      simp only [star176, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hxstar
      rcases hxstar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd (show (0:ℕ) = b by simpa using hxb) (by omega)
    have := Finset.card_le_card hsub
    simpa using this
  refine ⟨b, ?_⟩
  show (F.filter (fun e => e.1 = b)).card + (F.filter (fun e => e.2 = b)).card ≠ 2
  rw [h2]
  omega
