/-
Helper module for JSP-000093: the R(3,3) ≤ 6 argument.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace JSP000093

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))

/-- A triangle `t : Fin 3 → Fin n` is monochromatic for the edge coloring
`c` when its three edges get the same color (vertices distinct). -/
abbrev MonoTri {n : ℕ} (c : Fin n → Fin n → Bool) (t : Fin 3 → Fin n) : Prop :=
  c (t 0) (t 1) = c (t 1) (t 2) ∧ c (t 1) (t 2) = c (t 0) (t 2) ∧
    t 0 ≠ t 1 ∧ t 1 ≠ t 2 ∧ t 0 ≠ t 2

/-- Number of red neighbors of vertex `0` among `1, …, 5`. -/
def reds (x : Fin 5 → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-- Number of blue neighbors of vertex `0` among `1, …, 5`. -/
def blues (x : Fin 5 → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = false)).card

/-- Among the five edges out of a vertex, at least three have one color
(pigeonhole for 5 into 2 classes; tiny exhaustive check). -/
theorem pigeon5 : ∀ x : Fin 5 → Bool, 3 ≤ reds x ∨ 3 ≤ blues x := by
  native_decide

/-- Three same-colored neighbors can be exhibited (tiny exhaustive check
over the `2^5` color patterns and `5^3` triples). -/
theorem extract3_true : ∀ x : Fin 5 → Bool, 3 ≤ reds x →
    ∃ s : Fin 3 → Fin 5, Function.Injective s ∧ ∀ i, x (s i) = true := by
  native_decide

theorem extract3_false : ∀ x : Fin 5 → Bool, 3 ≤ blues x →
    ∃ s : Fin 3 → Fin 5, Function.Injective s ∧ ∀ i, x (s i) = false := by
  native_decide

/-- The color of an edge is preserved by symmetry (red version). -/
theorem sym' {c : Fin 6 → Fin 6 → Bool} (hsym : ∀ i j, c i j = c j i) {i j : Fin 6}
    (h : c i j = true) : c j i = true := by
  rw [hsym]; exact h

/-- The color of an edge is preserved by symmetry (blue version). -/
theorem sym'f {c : Fin 6 → Fin 6 → Bool} (hsym : ∀ i j, c i j = c j i) {i j : Fin 6}
    (h : c i j = false) : c j i = false := by
  rw [hsym]; exact h

/-- Boolean trichotomy: among three colors, one equals `col` or all three
equal its negation (16-case check). -/
theorem three_or_flip (col b1 b2 b3 : Bool) :
    b1 = col ∨ b2 = col ∨ b3 = col ∨ (b1 = !col ∧ b2 = !col ∧ b3 = !col) := by
  cases col <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

/-- **R(3,3) ≤ 6**: every symmetric 2-coloring of the edges of `K₆` has a
monochromatic triangle (classical argument: among the five edges out of
vertex `0`, three share a color; either two of their endpoints are joined
in that color, closing a triangle with `0`, or the three endpoints form a
triangle in the other color). -/
theorem r33_le_6 : ∀ c : Fin 6 → Fin 6 → Bool,
    (∀ i j : Fin 6, c i j = c j i) → ∃ t : Fin 3 → Fin 6, MonoTri c t := by
  intro c hsym
  have key : ∀ (col : Bool) (s : Fin 3 → Fin 5), Function.Injective s →
      (∀ i, c 0 (Fin.succ (s i)) = col) →
      ∃ t : Fin 3 → Fin 6, MonoTri c t := by
    intro col s hsinj hs
    have hne : ∀ i, (0 : Fin 6) ≠ Fin.succ (s i) := fun i h =>
      absurd h.symm (Fin.succ_ne_zero (s i))
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have hab : Fin.succ (s 0) ≠ Fin.succ (s 1) :=
      fun h => h01 (hsinj (Fin.succ_injective 5 h))
    have hbd : Fin.succ (s 1) ≠ Fin.succ (s 2) :=
      fun h => h12 (hsinj (Fin.succ_injective 5 h))
    have had : Fin.succ (s 0) ≠ Fin.succ (s 2) :=
      fun h => h02 (hsinj (Fin.succ_injective 5 h))
    cases three_or_flip col (c (Fin.succ (s 0)) (Fin.succ (s 1)))
        (c (Fin.succ (s 1)) (Fin.succ (s 2))) (c (Fin.succ (s 2)) (Fin.succ (s 0))) with
    | inl h1 =>
      cases h1 with
      | inl h2 =>
        exact ⟨fun i => if i = 0 then (0 : Fin 6) else
            if i = 1 then Fin.succ (s 0) else Fin.succ (s 1),
          by show c 0 (Fin.succ (s 0)) = c (Fin.succ (s 0)) (Fin.succ (s 1)); rw [hs 0, h2],
          by show c (Fin.succ (s 0)) (Fin.succ (s 1)) = c 0 (Fin.succ (s 1)); rw [h2, hs 1],
          by show (0 : Fin 6) ≠ Fin.succ (s 0); exact hne 0,
          by show Fin.succ (s 0) ≠ Fin.succ (s 1); exact hab,
          by show (0 : Fin 6) ≠ Fin.succ (s 1); exact hne 1⟩
      | inr h2 =>
        exact ⟨fun i => if i = 0 then (0 : Fin 6) else
            if i = 1 then Fin.succ (s 1) else Fin.succ (s 2),
          by show c 0 (Fin.succ (s 1)) = c (Fin.succ (s 1)) (Fin.succ (s 2)); rw [hs 1, h2],
          by show c (Fin.succ (s 1)) (Fin.succ (s 2)) = c 0 (Fin.succ (s 2)); rw [h2, hs 2],
          by show (0 : Fin 6) ≠ Fin.succ (s 1); exact hne 1,
          by show Fin.succ (s 1) ≠ Fin.succ (s 2); exact hbd,
          by show (0 : Fin 6) ≠ Fin.succ (s 2); exact hne 2⟩
    | inr h1 =>
      cases h1 with
      | inl h2 =>
        exact ⟨fun i => if i = 0 then (0 : Fin 6) else
            if i = 1 then Fin.succ (s 2) else Fin.succ (s 0),
          by show c 0 (Fin.succ (s 2)) = c (Fin.succ (s 2)) (Fin.succ (s 0)); rw [hs 2, h2],
          by show c (Fin.succ (s 2)) (Fin.succ (s 0)) = c 0 (Fin.succ (s 0)); rw [h2, hs 0],
          by show (0 : Fin 6) ≠ Fin.succ (s 2); exact hne 2,
          by show Fin.succ (s 2) ≠ Fin.succ (s 0); exact had.symm,
          by show (0 : Fin 6) ≠ Fin.succ (s 0); exact hne 0⟩
      | inr h2 =>
        obtain ⟨h2ab, h2bd, h2da⟩ := h2
        refine ⟨fun i => if i = 0 then Fin.succ (s 0) else
          if i = 1 then Fin.succ (s 1) else Fin.succ (s 2), ?_, ?_, ?_, ?_, ?_⟩
        · show c (Fin.succ (s 0)) (Fin.succ (s 1)) = c (Fin.succ (s 1)) (Fin.succ (s 2))
          rw [h2ab, h2bd]
        · show c (Fin.succ (s 1)) (Fin.succ (s 2)) = c (Fin.succ (s 0)) (Fin.succ (s 2))
          rw [h2bd, sym'f hsym h2da]
        · exact hab
        · exact hbd
        · exact had
  cases pigeon5 (fun i => c 0 (Fin.succ i)) with
  | inl h =>
    cases extract3_true (fun i => c 0 (Fin.succ i)) h with
    | intro s hs2 => cases hs2 with
      | intro hsinj hs => exact key true s hsinj hs
  | inr h =>
    cases extract3_false (fun i => c 0 (Fin.succ i)) h with
    | intro s hs2 => cases hs2 with
      | intro hsinj hs => exact key false s hsinj hs

end JSP000093
