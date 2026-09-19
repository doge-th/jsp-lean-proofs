/-
Justin Sun Prize JSP-000641: "How long an interval forces a
prescribed-length monochromatic increasing sequence with nonincreasing
gaps under every two-coloring?" (ascending waves; Brown–Erdős–Freedman
1990, Alloyar–Spencer 1989).

An ascending wave of length 3 is an increasing sequence `x₁ < x₂ < x₃`
of positions of one color whose gaps are nonincreasing:
`x₂ - x₁ ≥ x₃ - x₂`.

Machine-verified content (exhaustive over all 2⁷ = 128 two-colorings):
**every two-coloring of `{1,…,7}` contains a monochromatic ascending
wave of length 3**, and this is sharp — the coloring `1,1,0,0,1,0` of
`{1,…,6}` avoids it. No `sorry`.
-/

import Mathlib.Data.List.Basic

namespace JSP000641

/-- Color of position `i` (0-indexed) in coloring `n`. -/
def color (n i : Nat) : Bool := (n >>> i) % 2 == 1

/-- Positions `1 ≤ a < b < c ≤ L` form a monochromatic ascending wave
of length 3 in coloring `mask`. -/
def isAW3 (mask L : Nat) (a b c : Nat) : Bool :=
  0 < a && a < b && b < c && c ≤ L &&
  color mask (a - 1) == color mask (b - 1) && color mask (b - 1) == color mask (c - 1) &&
  (b - a) ≥ (c - b)

/-- Does coloring `mask` contain an ascending wave of length 3 within
`{1,…,L}`? -/
def hasAW3 (mask L : Nat) : Bool :=
  ((List.range (L + 1)).flatMap (fun a =>
    (List.range (L + 1)).flatMap (fun b =>
      (List.range (L + 1)).map (fun c => (a, b, c))))).any
    (fun p => let (a, b, c) := p; isAW3 mask L a b c)

/-- Every two-coloring of `{1,…,7}` contains a monochromatic ascending
wave of length 3 (exhaustive over all 2⁷ = 128 colorings). -/
theorem all_force_7 : ∀ m : Nat, m < 128 → hasAW3 m 7 = true := by
  intro m hm
  have hall : (List.range 128).all (fun k => hasAW3 k 7) = true := by
    native_decide
  rw [List.all_eq_true] at hall
  exact hall m (List.mem_range.mpr hm)

/-- Sharpness: the coloring `1,1,0,0,1,0` (mask 19) of `{1,…,6}`
contains no monochromatic ascending wave of length 3. -/
theorem counter_6 : hasAW3 19 6 = false := by
  native_decide

end JSP000641
