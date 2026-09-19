/-
Justin Sun Prize JSP-001018: "Must every sufficiently long integer
sequence with bounded gaps have two distinct consecutive blocks with
equal sums?"

Finite core, machine-verified: **every 4-gap integer sequence with all
gaps equal to 1 or 2 has two adjacent consecutive blocks of equal sum.**
Adjacent blocks `(x_{i+1}…x_j)`, `(x_{j+1}…x_k)` have equal sum iff the
prefix sums satisfy `S_j - S_i = S_k - S_j`; over 4 gaps the ten
`(i,j,k)` triples with `i<j<k≤4` give exactly the ten gap identities
listed in `eqBlocksTrue` (all contiguous-slab equalities). Exhaustive
over all 2⁴ = 16 gap tuples by `native_decide`. No `sorry`.
-/

namespace JSP001018

/-- The ten triples `(i,j,k)`, `0 ≤ i < j < k ≤ 4`, translate to the
ten contiguous-slab sum equalities over the gaps. -/
@[reducible]
def eqBlocksTrue (d1 d2 d3 d4 : Nat) : Prop :=
  d1 = d2 ∨ d1 = d2 + d3 ∨ d1 = d2 + d3 + d4 ∨
  d1 + d2 = d3 ∨ d1 + d2 = d3 + d4 ∨ d1 + d2 + d3 = d4 ∨
  d2 = d3 ∨ d2 = d3 + d4 ∨ d2 + d3 = d4 ∨ d3 = d4

theorem c0 : eqBlocksTrue 1 1 1 1 := by native_decide
theorem c1 : eqBlocksTrue 2 1 1 1 := by native_decide
theorem c2 : eqBlocksTrue 1 2 1 1 := by native_decide
theorem c3 : eqBlocksTrue 2 2 1 1 := by native_decide
theorem c4 : eqBlocksTrue 1 1 2 1 := by native_decide
theorem c5 : eqBlocksTrue 2 1 2 1 := by native_decide
theorem c6 : eqBlocksTrue 1 2 2 1 := by native_decide
theorem c7 : eqBlocksTrue 2 2 2 1 := by native_decide
theorem c8 : eqBlocksTrue 1 1 1 2 := by native_decide
theorem c9 : eqBlocksTrue 2 1 1 2 := by native_decide
theorem c10 : eqBlocksTrue 1 2 1 2 := by native_decide
theorem c11 : eqBlocksTrue 2 2 1 2 := by native_decide
theorem c12 : eqBlocksTrue 1 1 2 2 := by native_decide
theorem c13 : eqBlocksTrue 2 1 2 2 := by native_decide
theorem c14 : eqBlocksTrue 1 2 2 2 := by native_decide
theorem c15 : eqBlocksTrue 2 2 2 2 := by native_decide

end JSP001018
