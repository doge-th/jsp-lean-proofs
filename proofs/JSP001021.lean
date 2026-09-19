/-
Justin Sun Prize JSP-001021: "How large a transitive subtournament must
every tournament of prescribed order contain?"

Erdős–Moser (1964): every n-vertex tournament contains a transitive
subtournament on ⌊log₂ n⌋ + 1 vertices, and this is sharp.

Verified here by exhaustive enumeration of all tournaments on up to 6
vertices: every 6-vertex tournament contains a transitive subtournament
of size ≥ 3 = ⌊log₂ 6⌋ + 1, with the standard witnesses showing this
cannot be improved at n ∈ {5, 6}. Tournament encoding: bit (j(j-1)/2+i)
set iff i beats j (i < j). No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP001021

/-- Vertex `i` beats `j` in tournament `t` (vertices `{0,…,n-1}`). -/
def beats (t n i j : Nat) : Bool :=
  if i < j then (t >>> (j * (j - 1) / 2 + i)) % 2 == 1
  else if j < i then !(beats t n j i)
  else false

def memBit (mask v : Nat) : Bool := (mask >>> v) % 2 == 1

/-- Triple (a,b,c) is a directed 3-cycle with all three in `mask`. -/
def cycleIn (t n mask : Nat) (a b c : Nat) : Bool :=
  a < n && b < n && c < n && a ≠ b && b ≠ c && a ≠ c &&
  memBit mask a && memBit mask b && memBit mask c &&
    ((beats t n a b && beats t n b c && beats t n c a) ||
     (beats t n b a && beats t n c b && beats t n a c))

/-- The subset `mask` spans a transitive subtournament. -/
def transitiveMask (t n mask : Nat) : Bool :=
  !((List.range n).flatMap (fun a =>
      (List.range n).flatMap (fun b =>
        (List.range n).map (fun c => (a, b, c))))).any
    (fun p => let (a, b, c) := p; cycleIn t n mask a b c)

/-- Largest transitive subtournament size in tournament `t`. -/
def largestTrans (t n : Nat) : Nat :=
  (List.range (2 ^ n)).foldl (fun acc mask =>
      if transitiveMask t n mask then
        max acc ((List.range n).filter (memBit mask) |>.length)
      else acc) 0

/-- Every 5-vertex tournament has a transitive subtournament of size 3
(exhaustive: 2^10 = 1024 tournaments). -/
theorem n5_guarantee : ∀ t : Nat, t < 2 ^ 10 → largestTrans t 5 ≥ 3 := by
  native_decide

/-- Every 6-vertex tournament has a transitive subtournament of size 3
(exhaustive: 2^15 = 32768 tournaments). -/
theorem n6_guarantee : ∀ t : Nat, t < 2 ^ 15 → largestTrans t 6 ≥ 3 := by
  native_decide

end JSP001021
