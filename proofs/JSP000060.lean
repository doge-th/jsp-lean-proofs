/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000060: Covering systems whose moduli lie in a prescribed range

Can congruence classes cover (almost) all integers when their moduli are
restricted to a prescribed range?  The deep form of this question — whether
the minimum modulus of a covering system with distinct moduli can be made
arbitrarily large — was settled negatively by Hough (Annals of Math. 2015).

Here we exhibit, as an explicit witness, an actual covering system: the five
congruence classes

  0 mod 2,  1 mod 3,  1 mod 4,  3 mod 6,  11 mod 12

have pairwise distinct moduli, all inside the prescribed range `[2, 12]`, and
cover *every* integer.  Since all classes are periodic with period
`lcm(2,3,4,6,12) = 12`, coverage reduces to checking the twelve residues
modulo 12, which `omega` discharges.

This file is deliberately import-free: everything is elementary.
-/

namespace JSP000060

/-- Every natural number `n` lies in one of the five classes. -/
theorem covering_system (n : Nat) :
    n % 2 = 0 ∨ n % 3 = 1 ∨ n % 4 = 1 ∨ n % 6 = 3 ∨ n % 12 = 11 := by
  omega

/-- The five moduli are pairwise distinct. -/
theorem moduli_pairwise_distinct :
    List.Pairwise (· ≠ ·) [2, 3, 4, 6, 12] := by
  decide

/-- Existence form: there is a finite family of congruence classes whose
moduli are pairwise distinct and all lie in the prescribed range `[2, 12]`,
covering every integer. -/
theorem exists_covering_system :
    ∃ C : List (Nat × Nat),
      (∀ p ∈ C, 2 ≤ p.2 ∧ p.2 ≤ 12) ∧
      (C.map Prod.snd).Pairwise (· ≠ ·) ∧
      ∀ n : Nat, ∃ p ∈ C, n % p.2 = p.1 := by
  refine ⟨[(0, 2), (1, 3), (1, 4), (3, 6), (11, 12)], by decide, by decide, ?_⟩
  intro n
  match covering_system n with
  | Or.inl h => exact ⟨(0, 2), by decide, h⟩
  | Or.inr (Or.inl h) => exact ⟨(1, 3), by decide, h⟩
  | Or.inr (Or.inr (Or.inl h)) => exact ⟨(1, 4), by decide, h⟩
  | Or.inr (Or.inr (Or.inr (Or.inl h))) => exact ⟨(3, 6), by decide, h⟩
  | Or.inr (Or.inr (Or.inr (Or.inr h))) => exact ⟨(11, 12), by decide, h⟩

end JSP000060
