/-
Justin Sun Prize JSP-000653: "How large can a subset of an integer
interval be if all subset products are distinct?"

Exact maximal sizes for {2,…,n}, determined by exhaustive enumeration
and verified via native_decide. Element 1 is excluded since it forces
product collisions. Max sizes at even points n = 4..16: 3,4,5,6,7,8,9
(witness: the "staircase" 2,3,4,5,7,9,11,13,16 whose subset products
are all distinct). No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000653

def memElem (mask e : Nat) : Bool := (mask >>> (e - 1)) % 2 == 1

/-- All subset products of the subset encoded by `mask` (elements from
{1,…,n}), with multiplicity. -/
def subsetProducts (n mask : Nat) : List Nat :=
  (List.range n).foldl (fun acc e =>
    if memElem mask (e + 1) then acc ++ acc.map (fun p => p * (e + 1)) else acc) [1]

/-- The subset products are pairwise distinct. -/
def distinctProducts (n mask : Nat) : Bool :=
  let ps := subsetProducts n mask
  ps.all (fun p => ps.count p == 1)

/-- Size of the subset encoded by `mask` within {1,…,n}. -/
def sizeOf (mask n : Nat) : Nat :=
  (List.range n).filter (fun e => memElem mask (e + 1)) |>.length

/-- Maximal size of a subset of {2,…,n} with all subset products
distinct (excludes element 1). -/
def maxSize (n : Nat) : Nat :=
  (List.range (2 ^ n)).foldl (fun acc m =>
      if memElem m 1 then acc
      else if distinctProducts n m then max acc (sizeOf m n)
      else acc) 0

/-- Exact maximal sizes for n = 4, 6, 8, 10, 12, 14, 16 (the greedy
multiplicative staircase is optimal at these points). -/
theorem exact_sizes :
    maxSize 4 = 3 ∧ maxSize 6 = 4 ∧ maxSize 8 = 5 ∧ maxSize 10 = 6 ∧
    maxSize 12 = 7 ∧ maxSize 14 = 8 ∧ maxSize 16 = 9 := by
  native_decide

end JSP000653
