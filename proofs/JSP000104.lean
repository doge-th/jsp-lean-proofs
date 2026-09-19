/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000104: If a graph has neither a large clique nor a
large independent set, how many distinct edge counts do its induced
subgraphs attain?

Bounded case: the 5-cycle `C₅` has no clique of size 3 and no independent
set of size 3, and its induced subgraphs attain exactly the five distinct
edge counts `0, 1, 2, 3, 5` — verified exhaustively over all `2^5 = 32`
induced subgraphs.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace JSP000104

/-- Decidability of implication: helper instance so that bounded
`∀ … → …` statements admit `native_decide`. -/
instance instDecidableImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp, dq with
  | isFalse h, _ => isTrue (fun hp => absurd hp h)
  | _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun f => hq (f hp))


/-- Adjacency of the 5-cycle on vertices `Fin 5`. -/
def c5adj (i j : Fin 5) : Bool :=
  (i.val + 1) % 5 = j.val || (j.val + 1) % 5 = i.val

/-- Number of (undirected) cycle edges inside an induced vertex set `S`. -/
def e5 (S : Finset (Fin 5)) : ℕ :=
  (Finset.univ.filter fun p : Fin 5 × Fin 5 =>
    p.1.val < p.2.val ∧ p.1 ∈ S ∧ p.2 ∈ S ∧ c5adj p.1 p.2).card

/-- `C₅` has no triangle. -/
theorem no_clique3 :
    ∀ i j k : Fin 5, c5adj i j → c5adj j k → c5adj k i → False := by
  native_decide

/-- `C₅` has no independent set of size three. -/
theorem no_independent3 :
    ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      ¬c5adj i j → ¬c5adj j k → ¬c5adj k i → False := by
  native_decide

/-- The distinct edge counts attained by induced subgraphs of `C₅` are
exactly `0, 1, 2, 3, 5` — five values. -/
theorem c5_edge_counts :
    (Finset.univ.image e5) = {0, 1, 2, 3, 5} := by
  native_decide

/-- In particular five distinct edge counts are attained. -/
theorem five_distinct_counts :
    (Finset.univ.image e5).card = 5 := by
  native_decide

end JSP000104
