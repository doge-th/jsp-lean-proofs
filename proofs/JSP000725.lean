/-
Justin Sun Prize JSP-000725: "How large can an integer-interval subset
be if subset sums using different numbers of terms are never equal?"

A subset S ⊆ {1,…,n} is **weakly sum-distinct across layers**: whenever
A, B ⊆ S have different cardinalities, their sums differ. (Equivalently
the subsets of S split into sum layers by size, all disjoint.)

Machine-verified exact maxima by exhaustive enumeration (n = 1..6):
  n : 1 2 3 4 5 6
  max : 1 2 2 3 3 4
with witnesses (1,2), (1,2,4) etc. No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000725

def memElem (mask e : Nat) : Bool := (mask >>> (e - 1)) % 2 == 1

/-- Sum and size of the sub-subset `sub` (bit mask over elements
`1..n`) of the set `S` (mask). -/
def subSum (S sub n : Nat) : Nat :=
  (List.range n).foldl (fun acc e =>
      if memElem S (e + 1) && memElem sub (e + 1) then acc + (e + 1) else acc) 0

def subSize (S sub n : Nat) : Nat :=
  (List.range n).foldl (fun acc e =>
      if memElem S (e + 1) && memElem sub (e + 1) then acc + 1 else acc) 0

/-- The set `S` is weakly sum-distinct across layers: sub-subsets of
different sizes never share a sum. -/
def layersDistinct (S n : Nat) : Bool :=
  !((List.range (2 ^ n)).flatMap (fun a =>
      (List.range (2 ^ n)).map (fun b => (a, b)))).any
    (fun p => let (a, b) := p
              subSize S a n ≠ subSize S b n && subSum S a n = subSum S b n)

/-- Largest size of a weakly sum-distinct subset of `{1,…,n}`. -/
def setSize (S n : Nat) : Nat :=
  (List.range n).filter (fun e => memElem S (e + 1)) |>.length

def maxSize (n : Nat) : Nat :=
  (List.range (2 ^ n)).foldl (fun acc S =>
      if layersDistinct S n then max acc (setSize S n)
      else acc) 0

/-- Exact maxima for n = 1..6 (exhaustive). -/
theorem exact_sizes :
    maxSize 1 = 1 ∧ maxSize 2 = 2 ∧ maxSize 3 = 2 ∧
    maxSize 4 = 3 ∧ maxSize 5 = 3 ∧ maxSize 6 = 4 := by
  native_decide

end JSP000725
