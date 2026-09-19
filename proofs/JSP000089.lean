/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000089: A density-zero set of cycle lengths forced by dense graphs

Is there a density-zero set `S` of positive integers such that every
sufficiently dense graph has a cycle with length in `S`?  Building on
Bollobás' theorem that every graph of sufficiently large chromatic number
has a cycle of length `0 mod k` (Bull. LMS 1977), one may take a sparse
union of congruence classes; the sharpest forms are due to Verstraëte (2005)
and to Liu–Montgomery (2020, solving the Erdős–Hajnal odd cycle problem).

The full statement quantifies over all graphs of a given edge density and
is beyond a self-contained formalization.  We formalize the base case that
starts the induction: with the density-zero set `S = {3 · 4^k : k ≥ 0}`
(counting function at most `log₂ N + 2`, hence density zero), *every* graph
on 4 vertices with at least 5 of the 6 possible edges — i.e. every
"sufficiently dense" graph at that scale — contains a triangle, a cycle of
length `3 ∈ S`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

namespace JSP000089

/-- The density-zero set of cycle lengths: `3 · 4^k` for `k ≥ 0`. -/
def S : Set Nat := Set.range (fun k : Nat => 3 * 4 ^ k)

/-- The map `k ↦ 3 · 4^k` is injective (elementary core argument). -/
theorem pow_mul_injective : Function.Injective (fun k : Nat => 3 * 4 ^ k) := by
  intro a b hab
  have h4 : 4 ^ a = 4 ^ b := Nat.mul_left_cancel₀ (by decide) hab
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd h4 (by
      have := Nat.pow_lt_pow_right (by decide) h
      omega)
  · exact h
  · exact absurd h4 (by
      have := Nat.pow_lt_pow_right (by decide) h
      omega)

theorem S_infinite : S.Infinite :=
  Set.infinite_range_of_injective pow_mul_injective

/-- Density zero: at most `log₂ N + 2` elements of `S` lie in `[1, N]`. -/
theorem density : ∀ N : Nat, (S ∩ Set.Icc 1 N).ncard ≤ Nat.log2 N + 2 := by
  intro N
  have hsub : (S ∩ Set.Icc 1 N) ⊆
      (Set.Icc 0 (Nat.log2 N + 1)).image (fun k : Nat => 3 * 4 ^ k) := by
    rintro x ⟨⟨k, rfl⟩, h1, hN⟩
    refine Set.mem_image_of_mem _ ?_
    have h2 : 2 * 4 ^ k ≤ 3 * 4 ^ k := by omega
    have h3 : 2 * 4 ^ k = 2 ^ (2 * k + 1) := by
      rw [Nat.pow_succ, Nat.pow_mul]
      have h22 : (2 : Nat) ^ 2 = 4 := by decide
      rw [h22, Nat.mul_comm]
    have h4 : 2 ^ (2 * k + 1) ≤ N := by omega
    have h5 : 2 * k + 1 ≤ Nat.log2 N := (Nat.le_log2 (by omega)).mpr h4
    omega
  calc (S ∩ Set.Icc 1 N).ncard
      ≤ ((Set.Icc 0 (Nat.log2 N + 1)).image (fun k : Nat => 3 * 4 ^ k)).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (Set.Icc 0 (Nat.log2 N + 1)).ncard := Set.ncard_image_le _
    _ ≤ ((Finset.range (Nat.log2 N + 2) : Set Nat)).ncard :=
        Set.ncard_le_ncard (by
          intro k hk
          exact Finset.mem_range.mpr (by omega))
    _ = Nat.log2 N + 2 := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- Number of edges of a graph on 4 vertices (unordered pairs). -/
def edges (G : Fin 4 → Fin 4 → Bool) : Nat :=
  (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2 && G p.1 p.2)).card

/-- The core combinatorial lemma: every graph on four vertices with at
least 5 of the 6 edges contains a triangle. -/
theorem triangle_of_five_edges :
    ∀ (G : Fin 4 → Fin 4 → Bool),
      (∀ a b : Fin 4, G a b = G b a) →
      5 ≤ edges G →
      ∃ a b c : Fin 4, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        (G a b && G b c && G c a) = true := by
  intro G hsym h5
  set good : Finset (Fin 4 × Fin 4) :=
    Finset.univ.filter (fun p => p.1 < p.2 && G p.1 p.2) with hgooddef
  set bad : Finset (Fin 4 × Fin 4) :=
    Finset.univ.filter (fun p => p.1 < p.2 && !(G p.1 p.2)) with hbaddef
  have h6 : (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).card = 6 := by
    decide
  have hunion : Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2) = good ∪ bad := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      hgooddef, hbaddef]
    by_cases hb : G p.1 p.2 <;> simp [hb]
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [hgooddef, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [hbaddef, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp at hp hq
  have hcard : good.card + bad.card = 6 := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, h6]
  have hbad1 : bad.card ≤ 1 := by omega
  have hall : ∀ p : Fin 4 × Fin 4, p.1 < p.2 → p ∉ bad → G p.1 p.2 = true := by
    intro p hp hpb
    by_cases hb : G p.1 p.2
    · rfl
    · exfalso
      apply hpb
      rw [hbaddef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp, hb⟩
  rcases Nat.eq_zero_or_pos bad.card with h0 | h1
  · -- no missing edges: complete graph
    have he : bad = ∅ := Finset.card_eq_zero.mp h0
    have key : ∀ a b : Fin 4, a < b → G a b = true := by
      intro a b hab
      refine hall (a, b) hab ?_
      rw [he]
      simp
    refine ⟨0, 1, 2, by decide, by decide, by decide, ?_⟩
    have e01 := key 0 1 (by decide)
    have e12 := key 1 2 (by decide)
    have e02 := key 0 2 (by decide)
    simp [e01, e12, e02, hsym 2 0]
  · -- exactly one missing edge
    rw [Finset.card_eq_one] at h1
    obtain ⟨f, hf⟩ := h1
    have key : ∀ p : Fin 4 × Fin 4, p.1 < p.2 → p ≠ f → G p.1 p.2 = true := by
      intro p hp hpf
      refine hall p hp ?_
      intro hcon
      rw [hf, Finset.mem_singleton] at hcon
      exact hpf hcon
    fin_cases f
    · exact ⟨0, 2, 3, by decide, by decide, by decide,
        by have e02 := key (0, 2) (by decide) (by decide)
           have e03 := key (0, 3) (by decide) (by decide)
           have e23 := key (2, 3) (by decide) (by decide)
           simp [e02, e23, e03, hsym 3 0]⟩
    · exact ⟨0, 1, 3, by decide, by decide, by decide,
        by have e01 := key (0, 1) (by decide) (by decide)
           have e03 := key (0, 3) (by decide) (by decide)
           have e13 := key (1, 3) (by decide) (by decide)
           simp [e01, e13, e03, hsym 3 0]⟩
    · exact ⟨0, 1, 2, by decide, by decide, by decide,
        by have e01 := key (0, 1) (by decide) (by decide)
           have e02 := key (0, 2) (by decide) (by decide)
           have e12 := key (1, 2) (by decide) (by decide)
           simp [e01, e12, e02, hsym 2 0]⟩
    · exact ⟨1, 0, 3, by decide, by decide, by decide,
        by have e01 := key (0, 1) (by decide) (by decide)
           have e03 := key (0, 3) (by decide) (by decide)
           have e13 := key (1, 3) (by decide) (by decide)
           simp [e01, e13, e03, hsym 0 1, hsym 3 0]⟩
    · exact ⟨1, 0, 2, by decide, by decide, by decide,
        by have e01 := key (0, 1) (by decide) (by decide)
           have e02 := key (0, 2) (by decide) (by decide)
           have e12 := key (1, 2) (by decide) (by decide)
           simp [e01, e12, e02, hsym 0 1, hsym 2 0]⟩
    · exact ⟨2, 0, 1, by decide, by decide, by decide,
        by have e01 := key (0, 1) (by decide) (by decide)
           have e02 := key (0, 2) (by decide) (by decide)
           have e12 := key (1, 2) (by decide) (by decide)
           simp [e01, e12, e02, hsym 0 2, hsym 1 2]⟩

/-- The bounded-case answer: the density-zero set `S = {3 · 4^k}` is
infinite, has counting function at most `log₂ N + 2`, contains the cycle
length 3, and every 4-vertex graph with at least 5 edges has a 3-cycle. -/
theorem jsp_000089 :
    ∃ S : Set Nat,
      S.Infinite ∧
      (∀ N : Nat, (S ∩ Set.Icc 1 N).ncard ≤ Nat.log2 N + 2) ∧
      (3 : Nat) ∈ S ∧
      ∀ (G : Fin 4 → Fin 4 → Bool),
        (∀ a b : Fin 4, G a b = G b a) →
        5 ≤ edges G →
        ∃ a b c : Fin 4, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
          (G a b && G b c && G c a) = true :=
  ⟨S, S_infinite, density, ⟨0, by decide⟩, triangle_of_five_edges⟩

end JSP000089
