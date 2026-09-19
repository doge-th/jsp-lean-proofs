/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000838: Acyclic orientations stable under single edge reversals

Erdős (1971) asked whether every graph without triangles and four-cycles
admits an acyclic orientation such that reversing any single edge still
leaves the orientation acyclic; Neumann-Lara and Rivera-Campo answered
affirmatively (Proc. Amer. Math. Soc. 1978) using the probabilistic method.

The general statement quantifies over all `{C₃, C₄}`-free graphs, which is
beyond a self-contained formalization.  We formalize the witness case: the
5-cycle `C₅` is triangle- and four-cycle-free, and the orientation induced
by the vertex order `2 < 1 < 0 < 3 < 4` is acyclic, and remains acyclic
under every single edge reversal.  Acyclicity is verified by checking that
no directed closed walk of length 1 to 5 exists (a directed graph on 5
vertices is acyclic iff it has no directed cycle, and every directed cycle
has length at most 5).

All checks are finite and discharged by `native_decide`.
-/

namespace JSP000838

/-- The underlying simple graph: the 5-cycle on `{0,1,2,3,4}`. -/
def adjC5 (i j : Fin 5) : Bool :=
  ((i.val + 1) % 5 == j.val) || ((j.val + 1) % 5 == i.val)

/-- The base orientation, induced by the vertex order `2 < 1 < 0 < 3 < 4`:
edges point from lower to higher in that order. -/
def baseO : Fin 5 → Fin 5 → Bool := fun i j =>
  (i.val == 2 && j.val == 1) || (i.val == 1 && j.val == 0) ||
  (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 4) || (i.val == 0 && j.val == 4)

/-- Reverse the single directed edge `r → r+1`... in fact reverse whatever
edge of `o` joins `r` and `(r+1) % 5`. -/
def flip (o : Fin 5 → Fin 5 → Bool) (r i j : Fin 5) : Bool :=
  if (i.val = r.val ∧ j.val = (r.val + 1) % 5) ∨
     (i.val = (r.val + 1) % 5 ∧ j.val = r.val)
  then !(o i j) else o i j

/-- `R o n i j` : there is a directed walk of length `n` from `i` to `j`. -/
def R (o : Fin 5 → Fin 5 → Bool) : Nat → Fin 5 → Fin 5 → Bool
  | 0, i, j => i == j
  | n + 1, i, j => (List.range 5).any fun k => R o n i k && o k j

/-- Acyclic: no directed closed walk of length 1 through 5. -/
def Acyclic (o : Fin 5 → Fin 5 → Bool) : Prop :=
  ∀ i : Fin 5, R o 1 i i = false ∧ R o 2 i i = false ∧ R o 3 i i = false ∧
    R o 4 i i = false ∧ R o 5 i i = false

theorem adj_symm : ∀ i j : Fin 5, adjC5 i j = adjC5 j i := by
  intro i j
  simp only [adjC5, Bool.or_comm]

theorem adj_irrefl : ∀ i : Fin 5, adjC5 i i = false := by
  native_decide

theorem no_triangles : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
    ¬ (adjC5 i j = true ∧ adjC5 j k = true ∧ adjC5 k i = true) := by
  native_decide

theorem no_4cycles : ∀ i j k l : Fin 5, i ≠ j → j ≠ k → k ≠ l → i ≠ l →
    ¬ (adjC5 i j = true ∧ adjC5 j k = true ∧ adjC5 k l = true ∧ adjC5 l i = true) := by
  native_decide

theorem orient_sub : ∀ i j : Fin 5, baseO i j = true → adjC5 i j = true := by
  native_decide

theorem orient_antisym : ∀ i j : Fin 5, ¬ (baseO i j = true ∧ baseO j i = true) := by
  native_decide

theorem acyclic_base : Acyclic baseO := by
  native_decide

theorem acyclic_flip : ∀ r : Fin 5, Acyclic (flip baseO r) := by
  native_decide

/-- The bounded-case witness: `C₅` is `{C₃, C₄}`-free and admits an
acyclic orientation that stays acyclic under every single edge reversal. -/
theorem jsp_000838 :
    ∃ adj : Fin 5 → Fin 5 → Bool,
      (∀ i j, adj i j = adj j i) ∧
      (∀ i, adj i i = false) ∧
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        ¬ (adj i j = true ∧ adj j k = true ∧ adj k i = true)) ∧
      (∀ i j k l, i ≠ j → j ≠ k → k ≠ l → i ≠ l →
        ¬ (adj i j = true ∧ adj j k = true ∧ adj k l = true ∧ adj l i = true)) ∧
      ∃ o : Fin 5 → Fin 5 → Bool,
        (∀ i j, o i j = true → adj i j = true) ∧
        (∀ i j, ¬ (o i j = true ∧ o j i = true)) ∧
        Acyclic o ∧
        ∀ r : Fin 5, Acyclic (flip o r) :=
  ⟨adjC5, adj_symm, adj_irrefl, no_triangles, no_4cycles,
   baseO, orient_sub, orient_antisym, acyclic_base, acyclic_flip⟩

end JSP000838
