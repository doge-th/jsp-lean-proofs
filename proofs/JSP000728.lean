/-
Justin Sun Prize JSP-000728: "How many inclusion-maximal sum-free subsets
does a finite integer interval have?"

Exact counts for n = 1..12 determined by exhaustive enumeration over all
2^n subsets with maximality checks, machine-verified via `native_decide`.
Counts: 1, 2, 2, 4, 5, 6, 8, 13, 17, 23, 29, 37.

A subset of {1,…,n} (bit mask) is sum-free when no x, y, z ∈ S satisfy
x + y = z, and inclusion-maximal when no single element of the
complement can be added while staying sum-free. No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000728

/-- Element `e ∈ {1,…,n}` is in the subset encoded by `mask`. -/
def memElem (mask e : Nat) : Bool := (mask >>> (e - 1)) % 2 == 1

/-- Sum-free as before. -/
def isSumFree (n mask : Nat) : Bool :=
  (List.range n).all fun x =>
    (List.range n).all fun y =>
      let a := x + 1; let b := y + 1; let c := a + b
      c > n || !(memElem mask a && memElem mask b && memElem mask c)

/-- Inclusion-maximal: sum-free and adding any missing element breaks it. -/
def isMaximalSumFree (n mask : Nat) : Bool :=
  isSumFree n mask &&
  (List.range n).all fun e =>
    let a := e + 1
    memElem mask a || !(isSumFree n (mask + 2 ^ e))

/-- Count of inclusion-maximal sum-free subsets of `{1,…,n}`. -/
def countMaximalSumFree (n : Nat) : Nat :=
  (List.range (2 ^ n)).filter (isMaximalSumFree n) |>.length

/-- Exact counts for n = 1..12, exhaustively verified. -/
theorem counts_verified :
    countMaximalSumFree 1 = 1 ∧ countMaximalSumFree 2 = 2 ∧
    countMaximalSumFree 3 = 2 ∧ countMaximalSumFree 4 = 4 ∧
    countMaximalSumFree 5 = 5 ∧ countMaximalSumFree 6 = 6 ∧
    countMaximalSumFree 7 = 8 ∧ countMaximalSumFree 8 = 13 ∧
    countMaximalSumFree 9 = 17 ∧ countMaximalSumFree 10 = 23 ∧
    countMaximalSumFree 11 = 29 ∧ countMaximalSumFree 12 = 37 := by
  native_decide

end JSP000728
