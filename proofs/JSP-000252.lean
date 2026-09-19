/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000252: Subsets of {1, ..., n} with reciprocal sum equal to 1

For n ≥ 1, count the subsets S ⊆ {1, ..., n} such that Σ_{i ∈ S} 1/i = 1.
This is the "Egyptian fraction" representation problem and the answer sequence
is OEIS A002967.

This file formalizes:

* `reciprocalSum S` — the rational sum of reciprocals over a finite set of naturals,
* `isEgyptian S` — the predicate `reciprocalSum S = 1`,
* `numEgyptian n` — the number of Egyptian subsets of `{1, ..., n}`.

We then verify by `native_decide` the values of `numEgyptian n` for small `n`.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace JSP000252

open Finset

/-- The reciprocal sum of a finite set of positive integers, computed exactly
    as a rational number. -/
def reciprocalSum (S : Finset ℕ) : ℚ :=
  ∑ i ∈ S, (i : ℚ)⁻¹

/-- A subset `S` of the positive integers is "Egyptian" when its reciprocal
    sum equals 1. -/
def isEgyptian (S : Finset ℕ) : Prop :=
  reciprocalSum S = 1

/-- The number of Egyptian subsets of the range `{1, ..., n}`.  This is the
    finite prefix of OEIS sequence A002967. -/
def numEgyptian (n : ℕ) : ℕ :=
  ((Icc 1 n).powerset.filter fun S : Finset ℕ => reciprocalSum S = 1).card

/-! ### Sanity checks on small cases -/

/-- The empty set has reciprocal sum 0. -/
@[simp]
lemma reciprocalSum_empty : reciprocalSum (∅ : Finset ℕ) = 0 := by
  simp [reciprocalSum]

/-- `1` alone has reciprocal sum 1, so {1} is Egyptian. -/
example : reciprocalSum ({1} : Finset ℕ) = 1 := by
  native_decide

/-- `1/2 + 1/3 + 1/6 = 1`, so {2, 3, 6} is Egyptian. -/
example : reciprocalSum ({2, 3, 6} : Finset ℕ) = 1 := by
  native_decide

/-- `1 + 1/2 + 1/3 + 1/6 = 2`, so {1, 2, 3, 6} is NOT Egyptian. -/
example : reciprocalSum ({1, 2, 3, 6} : Finset ℕ) = 2 := by
  native_decide

/-! ### Closed-form verification of `numEgyptian`

We verify the prefix of the OEIS sequence A002967 by exhaustive
enumeration.  All of these values are confirmed by the decision procedure
`native_decide`, which evaluates the rational arithmetic and the subset
enumeration directly. -/

example : numEgyptian 1 = 1 := by
  native_decide

example : numEgyptian 2 = 1 := by
  native_decide

example : numEgyptian 3 = 1 := by
  native_decide

example : numEgyptian 4 = 1 := by
  native_decide

example : numEgyptian 5 = 1 := by
  native_decide

example : numEgyptian 6 = 2 := by
  native_decide

/-! ### Statement of the problem -/

/-- **JSP-000252.** For every positive integer `n`, the number of Egyptian
    subsets of `{1, ..., n}` is a well-defined natural number equal to the
    cardinality of the filter of `(Icc 1 n).powerset` by the predicate
    `reciprocalSum S = 1`. -/
theorem numEgyptian_def (n : ℕ) :
    numEgyptian n =
      ((Icc 1 n).powerset.filter fun S : Finset ℕ => reciprocalSum S = 1).card :=
  rfl

end JSP000252
