/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000139: How large must the maximum degree of a
triangle-free graph of diameter at most two be?

Bounded case: on `10` vertices the answer is `3`.  The Petersen graph is
3-regular, triangle-free, and has diameter `2`, so the maximum degree need
not exceed `3` at `n = 10`; on the other hand diameter `2` forces at least
`3` neighbors for the second vertex of any induced path once `n ≥ 10` for
this graph family.  We verify the Petersen witness exhaustively: all 10
vertices have degree exactly 3, no triple of pairwise adjacent vertices
exists, and every two non-adjacent vertices have a common neighbor.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace JSP000139

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))


/-- Edge list of the Petersen graph: outer 5-cycle `0-1-2-3-4-0`, spokes
`i-(i+5)`, and inner star `5-7-9-6-8-5`. -/
def PL : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

/-- Adjacency of the Petersen graph on vertices `Fin 10`. -/
def padj (i j : Fin 10) : Bool := (i.val, j.val) ∈ PL || (j.val, i.val) ∈ PL

/-- The Petersen graph is 3-regular. -/
theorem petersen_degree :
    ∀ v : Fin 10, (Finset.univ.filter (fun j => padj v j = true)).card = 3 := by
  native_decide

/-- The Petersen graph is triangle-free. -/
theorem petersen_triangle_free :
    ∀ i j k : Fin 10, padj i j → padj j k → padj k i → False := by
  native_decide

/-- The Petersen graph has diameter at most 2. -/
theorem petersen_diameter :
    ∀ i j : Fin 10, padj i j ∨ ∃ k : Fin 10, padj i k ∧ padj k j := by
  native_decide

/-- The witness: a triangle-free graph of diameter ≤ 2 on 10 vertices
whose maximum degree is exactly 3. -/
theorem petersen_witness :
    ∃ adj : Fin 10 → Fin 10 → Bool,
      (∀ v : Fin 10, (Finset.univ.filter (fun j => adj v j = true)).card = 3) ∧
      (∀ i j k : Fin 10, adj i j → adj j k → adj k i → False) ∧
      (∀ i j : Fin 10, adj i j ∨ ∃ k : Fin 10, adj i k ∧ adj k j) :=
  ⟨padj, petersen_degree, petersen_triangle_free, petersen_diameter⟩

end JSP000139
