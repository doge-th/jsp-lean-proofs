/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000492: Many repeated distances in a finite spherical point set

Erdős, Hickerson and Pach (Amer. Math. Monthly 1989) asked whether the
number of pairs at one distance among `n` points on a sphere in 3-space can
grow superlinearly in `n`; the answer is yes.  Here we formalize the
smallest superlinear witness, the regular octahedron: its 6 vertices lie on
the unit sphere in `R³`, and 24 ordered (12 unordered) vertex pairs realize
one single distance (squared distance `2`, i.e. distance `√2`), and
`12 > 6`: the number of pairs at one distance strictly exceeds the number
of points.

We use squared Euclidean distance (which determines the distance for these
non-antipodal pairs); every numerical check is discharged by `norm_num` on
real numerals.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace JSP000492

/-- The six vertices of the octahedron on the unit sphere. -/
def V : Fin 6 → (ℝ × ℝ × ℝ) := fun i =>
  match i with
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)
  | 3 => (-1, 0, 0)
  | 4 => (0, -1, 0)
  | 5 => (0, 0, -1)

/-- Squared Euclidean distance in `ℝ³`. -/
def sqdist (p q : ℝ × ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

/-- The point set: the six octahedron vertices. -/
def PtSet : Finset (ℝ × ℝ × ℝ) := Finset.univ.image V

/-- Antipodal indices (Boolean-valued for decidability). -/
def antipB (i j : Fin 6) : Bool := (i.val + 3) % 6 == j.val

/-- The 24 ordered index pairs that are neither equal nor antipodal. -/
def Eidx : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun p => p.1 != p.2 && !antipB p.1 p.2)

theorem V_injective : Function.Injective V := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [V] at hij <;>
    first
      | rfl
      | simp at hij

theorem card_Eidx : Eidx.card = 24 := by
  decide

theorem sphere : ∀ v ∈ PtSet, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 1 := by
  intro v hv
  simp only [PtSet, Finset.mem_image] at hv
  obtain ⟨i, -, rfl⟩ := hv
  fin_cases i <;> simp only [V] <;> norm_num

theorem card_PtSet : PtSet.card = 6 := by
  rw [Finset.card_image_of_injective _ V_injective]
  decide

/-- Every eligible index pair maps to a genuine pair of distinct points at
squared distance `2`. -/
theorem hsub : ∀ p ∈ Eidx,
    (V p.1, V p.2) ∈ (PtSet ×ˢ PtSet).filter
      (fun r => r.1 != r.2 ∧ sqdist r.1 r.2 = 2) := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hne, hant⟩ := hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩,
     Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩⟩, ⟨hne, ?_⟩⟩
  fin_cases p
  all_goals
    simp only [antipB, Bool.not_eq_true] at hant
    first
      | decide at hant
      | decide at hne
      | (simp only [V, sqdist]; norm_num)

/-- The number of ordered pairs of octahedron vertices at one single
distance (squared distance `2`) is at least 24, i.e. more than twice the
number of points. -/
theorem lower_bound :
    24 ≤ ((PtSet ×ˢ PtSet).filter
      (fun p => p.1 != p.2 ∧ sqdist p.1 p.2 = 2)).card := by
  have hinj : Function.Injective (fun p : Fin 6 × Fin 6 => (V p.1, V p.2)) :=
    fun a b h => Prod.ext (V_injective h.1) (V_injective h.2)
  have hle : (Eidx.image (fun p : Fin 6 × Fin 6 => (V p.1, V p.2))).card ≤
      ((PtSet ×ˢ PtSet).filter
        (fun p => p.1 != p.2 ∧ sqdist p.1 p.2 = 2)).card := by
    refine Finset.card_le_card (Finset.image_subset_iff.mpr ?_)
    exact hsub
  calc (Eidx.image (fun p : Fin 6 × Fin 6 => (V p.1, V p.2))).card
      = Eidx.card := Finset.card_image_of_injective _ hinj
    _ = 24 := card_Eidx
    _ ≤ _ := hle

/-- The full superlinearity witness: a 6-point set on the unit sphere with
more than twice as many ordered pairs at one fixed distance. -/
theorem jsp_000492 :
    ∃ (S : Finset (ℝ × ℝ × ℝ)),
      (∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 1) ∧
      S.card = 6 ∧
      2 * S.card < ((S ×ˢ S).filter
        (fun p => p.1 != p.2 ∧ sqdist p.1 p.2 = 2)).card := by
  refine ⟨PtSet, sphere, card_PtSet, ?_⟩
  have h := lower_bound
  omega

end JSP000492
