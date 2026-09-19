/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000182: How long must an integer interval be to force
either a monochromatic or a rainbow arithmetic progression under every
coloring?

Answer (bounded instance, 2 colors, 3-term progressions): the interval
`{0, …, 8}` of length 9 works, and length 8 does not.  With only 2 colors a
rainbow 3-term progression is impossible, so the question is exactly the
van der Waerden problem W(2, 3) = 9: every 2-coloring of `{0, …, 8}`
contains a monochromatic 3-term arithmetic progression, while the coloring
of `{0, …, 7}` given by the bitmask `51 = 0b110011` (colors
`1,1,0,0,1,1,0,0`) avoids all monochromatic 3-term progressions.  The
universal claim is certified by a single exhaustive computation over all
`2^9` colorings; the sharpness witness `51` is checked directly.
-/


import Mathlib.Data.Finset.Card
/-- Color of point `i` under the coloring encoded by bitmask `k`
(bit `i` of `k`). -/
def col182 (k i : ℕ) : Bool := (k >>> i) % 2 == 1

/-- `apfree182 n k` is true iff the 2-coloring of `{0, …, n-1}` encoded by
`k` has no monochromatic 3-term arithmetic progression. -/
def apfree182 (n k : ℕ) : Bool :=
  (List.range ((n - 1) / 2)).all fun dd =>
    (List.range (n - 2 * (dd + 1))).all fun a =>
      !((col182 k a == col182 k (a + dd + 1)) &&
        (col182 k (a + dd + 1) == col182 k (a + 2 * (dd + 1))))

/-- JSP-000182: every 2-coloring of an interval of 9 consecutive integers
contains a monochromatic (hence monochromatic-or-rainbow) 3-term
arithmetic progression; 8 do not suffice. -/
theorem jsp_000182 :
    (∀ k : ℕ, k < 2 ^ 9 → apfree182 9 k = false) ∧
    ∃ k : ℕ, k < 2 ^ 8 ∧ apfree182 8 k = true := by
  refine ⟨fun k hk => ?_, ⟨51, by decide, by decide⟩⟩
  have hall : (List.range 512).all (fun k => apfree182 9 k == false) = true :=
    by native_decide
  have hk' : k ∈ List.range 512 := List.mem_range.2 hk
  have := List.all_eq_true.1 hall k hk'
  exact of_decide_eq_true this
