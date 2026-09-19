/-
Justin Sun Prize JSP-000616: "How many sum-free subsets do the first
several positive integers have?"

Exact counts for n = 1..8 determined by exhaustive enumeration over all
2^n subsets, machine-verified via `native_decide`. Counts (OEIS A007865
prefix): 2, 3, 6, 9, 16, 24, 42, 61.

A subset of {1,…,n} is encoded as a bit mask: element e ∈ {1,…,n} is in
the subset iff bit (e-1) of the mask is set. Sum-free: no x, y, z ∈ S
with x + y = z. No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000616

/-- Element `e ∈ {1,…,n}` is in the subset encoded by `mask`. -/
def memElem (mask e : Nat) : Bool := (mask >>> (e - 1)) % 2 == 1

/-- The subset encoded by `mask` ⊆ `{1,…,n}` is sum-free. -/
def isSumFree (n mask : Nat) : Bool :=
  (List.range n).all fun x =>
    (List.range n).all fun y =>
      let a := x + 1  -- element a ∈ {1,…,n}
      let b := y + 1
      let c := a + b
      c > n || !(memElem mask a && memElem mask b && memElem mask c)

/-- Count of sum-free subsets of `{1,…,n}`. -/
def countSumFree (n : Nat) : Nat :=
  (List.range (2 ^ n)).filter (isSumFree n) |>.length

/-- Exact counts for n = 1..8, exhaustively verified. -/
theorem counts_verified :
    countSumFree 1 = 2 ∧ countSumFree 2 = 3 ∧ countSumFree 3 = 6 ∧
    countSumFree 4 = 9 ∧ countSumFree 5 = 16 ∧ countSumFree 6 = 24 ∧
    countSumFree 7 = 42 ∧ countSumFree 8 = 61 := by
  native_decide

end JSP000616