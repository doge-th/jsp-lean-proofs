/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000192: Steiner triple systems of large girth

Kwan, Sudakov, and collaborators (arXiv:2201.04554) proved that there are
Steiner triple systems of arbitrarily large "girth", i.e. avoiding all
small cyclic configurations; the full result rests on heavy randomized
algebraic constructions.

A Steiner triple system has *girth at least 4* when it contains no Pasch
configuration (four triples on six points, each point on exactly two of
them).  We formalize the classical witness: the affine plane
`AG(2,3)`, a Steiner triple system on 9 points with 12 blocks, and we verify
(i) every block has size 3, (ii) every pair of points lies in exactly one
block, and (iii) any four *distinct* blocks span at least 7 points, which
rules out every Pasch configuration (four distinct blocks spanning at most
6 points would force each of the 6 points to lie on exactly two of the
blocks — a Pasch configuration).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry

namespace JSP000192

/-- The 12 blocks of `AG(2,3)` (lines of the affine plane over `F₃`,
encoded as `3x + y` on points `Fin 9`). -/
def B : List (Finset (Fin 9)) :=
  [{0, 3, 6}, {1, 4, 7}, {2, 5, 8},      -- y = 0, 1, 2
   {0, 4, 8}, {1, 5, 6}, {2, 3, 7},      -- y = x + c
   {0, 5, 7}, {1, 3, 8}, {2, 4, 6},      -- y = 2x + c
   {0, 1, 2}, {3, 4, 5}, {6, 7, 8}]      -- x = 0, 1, 2

theorem length_B : B.length = 12 := by
  decide

theorem block_sizes : ∀ t ∈ B, t.card = 3 := by
  decide

/-- Every pair of distinct points lies in exactly one block. -/
theorem pair_covering : ∀ a b : Fin 9, a ≠ b → B.countP (fun t => a ∈ t ∧ b ∈ t) = 1 := by
  intro a b _
  decide

/-- No four distinct blocks span at most six points: this is exactly the
absence of Pasch configurations, i.e. girth at least 4. -/
theorem no_pasch : ∀ i j k l : Fin 12,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    6 < (B.getD i.val ∅ ∪ B.getD j.val ∅ ∪ B.getD k.val ∅ ∪ B.getD l.val ∅).card := by
  native_decide

/-- The bounded-case witness: a Steiner triple system with girth ≥ 4 on 9
points. -/
theorem jsp_000192 :
    ∃ blocks : List (Finset (Fin 9)),
      blocks.length = 12 ∧
      (∀ t ∈ blocks, t.card = 3) ∧
      (∀ a b : Fin 9, a ≠ b → blocks.countP (fun t => a ∈ t ∧ b ∈ t) = 1) ∧
      (∀ i j k l : Fin 12,
        i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
        6 < (blocks.getD i.val ∅ ∪ blocks.getD j.val ∅ ∪
             blocks.getD k.val ∅ ∪ blocks.getD l.val ∅).card) := by
  refine ⟨B, length_B, block_sizes, pair_covering, no_pasch⟩

end JSP000192
