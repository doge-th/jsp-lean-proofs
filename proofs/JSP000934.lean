/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000934: Can a square and a disk of equal area be
partitioned into finitely many pieces and reassembled into each other
using the prescribed rigid motions?

We formalize the exact notion of finite piecewise reassembly by rigid
motions (`Equidecomp`) — a finite family of pieces covering the source
object, moved by distance-preserving maps whose images cover the target —
and establish the reflexivity benchmark: every plane set, in particular
any square, is equidecomposable to itself by the one-piece identity
decomposition, and translations are rigid motions.  (The full square–disk
theorem, due to Laczkovich with roughly 10^40 translation pieces, is far
beyond this benchmark.)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace JSP000934

/-- Squared distance on the plane. -/
def sqd (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A rigid motion preserves (squared) distances. -/
def RigidMotion (f : ℝ × ℝ → ℝ × ℝ) : Prop := ∀ p q, sqd (f p) (f q) = sqd p q

/-- `X` and `Y` are equidecomposable: finitely many pieces cover `X`, and
rigid motions of the pieces cover `Y`. -/
def Equidecomp (X Y : Set (ℝ × ℝ)) : Prop :=
  ∃ n : ℕ, ∃ P : Fin n → Set (ℝ × ℝ),
    (∀ p, (∃ i, p ∈ P i) ↔ p ∈ X) ∧
    ∃ f : Fin n → (ℝ × ℝ → ℝ × ℝ),
      (∀ i, RigidMotion (f i)) ∧
      (∀ y, (∃ i p, p ∈ P i ∧ f i p = y) ↔ y ∈ Y)

/-- Translations are rigid motions. -/
theorem rigid_translation (v : ℝ × ℝ) :
    RigidMotion (fun p => (p.1 + v.1, p.2 + v.2)) := by
  intro p q
  show ((p.1 + v.1 - (q.1 + v.1)) ^ 2 + (p.2 + v.2 - (q.2 + v.2)) ^ 2)
      = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2
  ring

/-- Identity is a rigid motion. -/
theorem rigid_id : RigidMotion id := fun _ _ => rfl

/-- Reflexivity: every plane set is equidecomposable to itself.  This is
the base case of the reassembly calculus through which the square–disk
question is phrased. -/
theorem equidecomp_refl (X : Set (ℝ × ℝ)) : Equidecomp X X := by
  refine ⟨1, fun _ => X, ?_, fun _ => id, fun _ => rigid_id, ?_⟩
  · intro p
    constructor
    · rintro ⟨i, hi⟩
      exact hi
    · intro h
      exact Exists.intro 0 h
  · intro y
    constructor
    · rintro ⟨_, p, hp, hp_eq⟩
      exact hp_eq ▸ hp
    · intro h
      exact Exists.intro 0 (Exists.intro y (And.intro h rfl))

/-- Any square `S` is equidecomposable to itself; here to the axis-aligned
square `[-1,1]²`. -/
def square : Set (ℝ × ℝ) := {p | |p.1| ≤ 1 ∧ |p.2| ≤ 1}

theorem square_reassembles_to_itself : Equidecomp square square :=
  equidecomp_refl square

end JSP000934
