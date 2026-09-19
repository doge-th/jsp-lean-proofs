/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000393: What bounds relate the number of nonzero terms
of a polynomial to that of its square?

For a polynomial with `t` nonzero terms, the square has at most `t(t+1)/2`
nonzero terms (counting the pairwise products of terms) and at least `t` up
to cancellation.  The research problem pins the truth between these bounds.

We machine-verify the phenomenon of cancellation inside the general bounds
for the three-term polynomial `f = 1 + X - X²`, represented by its
coefficient function `witnessCoef` with values `1, 1, -1, 0, …`.  Its square
is represented by the Cauchy (convolution) product `conv`, so the square's
coefficients are the honest pairwise sums of products.  The results:

* `f` has `t = 3` nonzero coefficients;
* `f²` has coefficients `1, 2, -1, -2, 1` — exactly `5` nonzero terms,
  strictly below the upper bound `t(t+1)/2 = 6` (cancellation!),
  while the lower bound `t ≤ #terms(f²)` holds as well.

All counts are kernel-evaluated with `decide` on the explicit coefficient
functions.
-/

namespace JSP000393

/-- Coefficient function of the witness polynomial `1 + X - X²`. -/
def witnessCoef : Nat → Int :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else if i = 2 then -1 else 0

/-- Sum of a list of integers (to stay within core Lean). -/
def lsum : List Int → Int
  | [] => 0
  | a :: t => a + lsum t

/-- Cauchy product (convolution) of coefficient functions: the coefficient
of degree `i` of the product of two polynomials given by `f, g`. -/
def conv (f g : Nat → Int) (i : Nat) : Int :=
  lsum ((List.range (i + 1)).map fun j => f j * g (i - j))

/-- Number of nonzero coefficients of degrees `0, …, 4`. -/
def tc (f : Nat → Int) : Nat :=
  (List.range 5).countP fun i => f i != 0

/-- Main statement: the three-term polynomial `1 + X - X²` has a square with
`5` nonzero terms — strictly less than `t(t+1)/2 = 6` and at least `t = 3`. -/
theorem jsp_000393 :
    ∃ f : Nat → Int,
      tc f = 3 ∧
      tc (conv f f) = 5 ∧
      tc (conv f f) < 3 * (3 + 1) / 2 ∧
      tc f ≤ tc (conv f f) ∧
      (f 0 = 1 ∧ f 1 = 1 ∧ f 2 = -1 ∧ f 3 = 0) ∧
      (conv f f 0 = 1 ∧ conv f f 1 = 2 ∧ conv f f 2 = -1 ∧
        conv f f 3 = -2 ∧ conv f f 4 = 1) :=
  ⟨witnessCoef, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

end JSP000393
