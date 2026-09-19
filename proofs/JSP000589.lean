/-
Justin Sun Prize JSP-000589: "How long an interval forces a three-term
arithmetic progression in one color?"

Answer (core content, machine-verified): **W(2,3) = 9 exactly**.
- Upper bound: every two-coloring of `{1,…,9}` contains a monochromatic
  3-term AP (all 512 colorings exhaustively checked).
- Sharpness: for every `n ≤ 8` there is a two-coloring of `{1,…,n}` with
  no monochromatic 3-AP (witness: prefixes of the alternating coloring
  204 = 0b00110011).

Method: colorings encoded as bitmasks (bit i = color of position i+1);
all checks via `native_decide` (decision procedure). Nontrivial progressions
only: the common difference `d ≥ 1`. No `sorry`.
-/

import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic

namespace JSP000589

/-- Color of 0-indexed position `i` in the coloring encoded by `n`:
bit `i` of `n`. -/
def color (n i : Nat) : Bool := (n >>> i) % 2 == 1

/-- All index pairs `(a, d)` with `d ≥ 1` and `a, a+d, a+2d` inside
`{0,…,k-1}` (the first `k` positions). -/
def apPairs (k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap fun a =>
    (List.range k).filterMap fun d =>
      if 0 < d ∧ a + d + d < k then some (a, d) else none

/-- Positions `a, a+d, a+2d` carry the same color. -/
def isMono3AP (n : Nat) (p : Nat × Nat) : Bool :=
  let (a, d) := p
  color n a == color n (a + d) && color n (a + d) == color n (a + d + d)

/-- Some monochromatic (nontrivial) 3-AP exists entirely within the
first `k` positions of coloring `n`. -/
def hasMono3APLen (n k : Nat) : Bool := (apPairs k).any (isMono3AP n)

/-! ## Upper bound: [1,9] always forces -/

/-- Every two-coloring of `{1,…,9}` contains a monochromatic
three-term arithmetic progression (exhaustive over 2⁹ = 512 colorings,
each checked against all `(a, d)` pairs with `d ≥ 1`). -/
theorem all_force_9 :
    ∀ n : Nat, n < 512 → hasMono3APLen n 9 = true := by
  intro n hn
  have hall : (List.range 512).all (fun m => hasMono3APLen m 9) = true := by
    native_decide
  rw [List.all_eq_true] at hall
  exact hall n (List.mem_range.mpr hn)

/-! ## Sharpness: [1,8] does not force -/

/-- For every `n ≤ 8` there is a two-coloring of `{1,…,n}` with no
monochromatic 3-AP: the low-bit prefix of the alternating coloring
`204 = 0b00110011` (colors 0,0,1,1,0,0,1,1 on positions 1..8). -/
theorem prefixes_free :
    ∀ n : Nat, n ≤ 8 → ∃ m, m < 2 ^ n ∧ hasMono3APLen m n = false := by
  intro n hn
  interval_cases n
  · exact ⟨0, by native_decide, by native_decide⟩
  · exact ⟨204 % 2, by native_decide, by native_decide⟩
  · exact ⟨204 % 4, by native_decide, by native_decide⟩
  · exact ⟨204 % 8, by native_decide, by native_decide⟩
  · exact ⟨204 % 16, by native_decide, by native_decide⟩
  · exact ⟨204 % 32, by native_decide, by native_decide⟩
  · exact ⟨204 % 64, by native_decide, by native_decide⟩
  · exact ⟨204 % 128, by native_decide, by native_decide⟩
  · exact ⟨204, by native_decide, by native_decide⟩

/-! ## Conclusion: W(2,3) = 9 exactly -/

/-- **W(2,3) = 9**: the least interval length that forces a
monochromatic three-term AP under every two-coloring. -/
theorem W2_3_exact :
    (∀ n : Nat, n < 512 → hasMono3APLen n 9 = true) ∧
    (∀ n : Nat, n ≤ 8 → ∃ m, m < 2 ^ n ∧ hasMono3APLen m n = false) :=
  ⟨all_force_9, prefixes_free⟩

end JSP000589