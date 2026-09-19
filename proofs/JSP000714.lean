/-
Justin Sun Prize JSP-000714: "How many Sidon subsets do the first
several positive integers have?"

Exact counts for n = 1..8 determined by exhaustive enumeration over all
2^n subsets, machine-verified via `native_decide`. Counts: 2, 4, 7, 13,
22, 36, 57, 91.

A subset S ⊆ {1,…,n} is Sidon when all pairwise sums `a + b` with
`a ≤ b` (a, b ∈ S) are distinct — i.e., two pairs with equal sum are the
same pair. Encoded as bit masks; `native_decide` checks every subset
against every pair of index pairs. No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000714

/-- Element `e ∈ {1,…,n}` is in the subset encoded by `mask`. -/
def memElem (mask e : Nat) : Bool := (mask >>> (e - 1)) % 2 == 1

/-- Sidon property for the subset encoded by `mask` ⊆ `{1,…,n}`:
if `a + b = c + d` with all four elements in the subset, then the
(ordered, a ≤ b) pairs coincide. -/
def isSidon (n mask : Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range n).all fun j =>
      (List.range n).all fun k =>
        (List.range n).all fun l =>
          let a := i + 1; let b := j + 1; let c := k + 1; let d := l + 1
          -- normalize: a ≤ b, c ≤ d
          let ab := if a ≤ b then (a, b) else (b, a)
          let cd := if c ≤ d then (c, d) else (d, c)
          let inS := memElem mask a && memElem mask b && memElem mask c && memElem mask d
          let sumsEq := a + b = c + d
          !(inS && sumsEq && !(ab == cd)) || (a > b || c > d)

/-- Count of Sidon subsets of `{1,…,n}`. -/
def countSidon (n : Nat) : Nat :=
  (List.range (2 ^ n)).filter (isSidon n) |>.length

/-- Exact counts for n = 1..8, exhaustively verified. -/
theorem counts_verified :
    countSidon 1 = 2 ∧ countSidon 2 = 4 ∧ countSidon 3 = 7 ∧
    countSidon 4 = 13 ∧ countSidon 5 = 22 ∧ countSidon 6 = 36 ∧
    countSidon 7 = 57 ∧ countSidon 8 = 91 := by
  native_decide

end JSP000714