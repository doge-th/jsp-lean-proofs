/-
Justin Sun Prize JSP-000733: "How large can an integer-interval subset
be if its distinct subset sums never divide one another?"

S ⊆ {1,…,n} is **division-free on subset sums**: among the sums of
nonempty subsets of S, no one divides a different one. Machine-verified
exact maxima by exhaustive enumeration (n = 1..9):
  n : 1 2 3 4 5 6 7 8 9
  max : 1 1 2 2 2 2 3 3 3
witnesses: {1}; {2,3}; {4,6,7}. No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000733

def memElem (mask e : Nat) : Bool := (mask >>> (e - 1)) % 2 == 1

/-- Sum of the sub-subset `sub` (same 1-based bit convention) of `S`. -/
def subSum (S sub n : Nat) : Nat :=
  (List.range n).foldl (fun acc e =>
      if memElem S (e + 1) && memElem sub (e + 1) then acc + (e + 1) else acc) 0

/-- Sub-subset `sub` is nonempty within `S`. -/
def nonempty (S sub n : Nat) : Bool :=
  (List.range n).any (fun e => memElem S (e + 1) && memElem sub (e + 1))

/-- Division-free: no two distinct nonempty subset sums with one
dividing the other. -/
def divFree (S n : Nat) : Bool :=
  !((List.range (2 ^ n)).flatMap (fun a =>
      (List.range (2 ^ n)).map (fun b => (a, b)))).any
    (fun p => let (a, b) := p
              nonempty S a n && nonempty S b n &&
              subSum S a n ≠ subSum S b n && (subSum S b n % subSum S a n) = 0)

def setSize (S n : Nat) : Nat :=
  (List.range n).filter (fun e => memElem S (e + 1)) |>.length

/-- Largest division-free subset of `{1,…,n}`. -/
def maxSize (n : Nat) : Nat :=
  (List.range (2 ^ n)).foldl (fun acc S =>
      if divFree S n then max acc (setSize S n) else acc) 0

/-- Exact maxima for n = 1..9 (exhaustive). -/
theorem exact_sizes :
    maxSize 1 = 1 ∧ maxSize 2 = 1 ∧ maxSize 3 = 2 ∧
    maxSize 4 = 2 ∧ maxSize 5 = 2 ∧ maxSize 6 = 2 ∧
    maxSize 7 = 3 ∧ maxSize 8 = 3 ∧ maxSize 9 = 3 := by
  native_decide

end JSP000733
