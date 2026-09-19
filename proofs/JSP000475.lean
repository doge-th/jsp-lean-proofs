/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000475: Can finitely many residue classes cover all
integers with no modulus dividing another?

Yes.  Take the moduli 6, 10, 15 (no one divides another, since each is a
product of exactly two of the primes 2, 3, 5) with the 13 residue classes

  n ≡ 0, 1, 2          (mod 6),
  n ≡ 1, 3, 5, 7, 9    (mod 10)   (i.e. n odd),
  n ≡ 1, 4, 7, 10, 13  (mod 15)   (i.e. n ≡ 1 mod 3).

Coverage: if `n % 6 ∈ {0, 1, 2}` the first family catches `n`; if `n % 6 = 3`
or `5` then `n` is odd and the mod-10 family catches it; if `n % 6 = 4` then
`n ≡ 1 (mod 3)` and the mod-15 family catches it.
-/

import Mathlib.Data.Nat.MaxPrimeFac

namespace JSP000475

/-- The covering condition, phrased through residues mod 6, 10 and 15. -/
theorem cover (n : ℕ) : n % 6 < 3 ∨ n % 10 % 2 = 1 ∨ n % 15 % 3 = 1 := by
  have h2 : n % 10 % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : (2 : ℕ) ∣ 10)
  have h3 : n % 15 % 3 = n % 3 := Nat.mod_mod_of_dvd n (by decide : (3 : ℕ) ∣ 15)
  have h6 : n % 6 % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : (2 : ℕ) ∣ 6)
  have h9 : n % 6 % 3 = n % 3 := Nat.mod_mod_of_dvd n (by decide : (3 : ℕ) ∣ 6)
  rcases Nat.lt_or_ge (n % 6) 3 with h | h
  · exact Or.inl h
  rcases Nat.lt_or_ge (n % 6) 4 with h4 | h4
  · right; left
    have hr : n % 6 = 3 := by omega
    rw [h2, ← h6, hr]
  rcases Nat.lt_or_ge (n % 6) 5 with h5 | h5
  · right; right
    have hr : n % 6 = 4 := by omega
    rw [h3, ← h9, hr]
  · right; left
    have hr : n % 6 = 5 := by omega
    rw [h2, ← h6, hr]

/-- JSP-000475: a finite covering system of ℕ whose moduli 6, 10, 15 are
pairwise incomparable under divisibility. -/
theorem jsp_000475 :
    ∃ (mods : Finset ℕ) (cls : ℕ → Finset ℕ),
      (∀ n : ℕ, ∃ m ∈ mods, n % m ∈ cls m) ∧
      (∀ a ∈ mods, ∀ b ∈ mods, a ∣ b → a = b) := by
  refine ⟨{6, 10, 15},
    fun m => if m = 6 then {0, 1, 2}
      else if m = 10 then {1, 3, 5, 7, 9} else {1, 4, 7, 10, 13},
    ?_, ?_⟩
  · intro n
    rcases cover n with h | h | h
    · refine ⟨6, by decide, ?_⟩
      show n % 6 ∈ ({0, 1, 2} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · refine ⟨10, by decide, ?_⟩
      show n % 10 ∈ ({1, 3, 5, 7, 9} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · refine ⟨15, by decide, ?_⟩
      show n % 15 ∈ ({1, 4, 7, 10, 13} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
        first
          | rfl
          | exact absurd hab (by decide)

end JSP000475
