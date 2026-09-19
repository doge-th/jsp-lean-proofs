/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000745: Finite colorings avoiding a prescribed sparse set of differences

Can the integers be finitely colored so that no two integers of the same
color differ by an element of a prescribed sparse set `S`?  For `S` a
lacunary sequence this is the study of chromatic numbers of Cayley graphs
on `Z` (Katznelson, Combinatorica 2001); Péter and Schram (2010) showed
that every lacunary set admits such a coloring, answering an Erdős question.

We prove the full affirmative statement for the canonical lacunary set: the
powers of two.  Let `S = {2^k : k ∈ Nat}` and color `x` by `x mod 3`.  A
same-colored pair has difference divisible by `3`, but `3 ∤ 2^k` for every
`k`.  Hence `S` is an infinite, density-zero (its counting function is at
most `log₂ N + 1`) set of differences that the 3-coloring `x ↦ x mod 3`
avoids.  (The distance between naturals `x, y` is `Nat.dist x y = |x - y|`.)
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

namespace JSP000745

/-- The prescribed sparse set of differences: the powers of two. -/
def S : Set Nat := Set.range (fun k : Nat => 2 ^ k)

/-- The 3-coloring: `x ↦ x mod 3`, viewed as a value in `Fin 3`. -/
def color (x : Nat) : Fin 3 := ⟨x % 3, by omega⟩

/-- Powers of two are never divisible by three. -/
theorem two_pow_mod_three_ne_zero (k : Nat) : 2 ^ k % 3 ≠ 0 := by
  have key : ∀ m : Nat, 2 ^ (2 * m) % 3 = 1 ∧ 2 ^ (2 * m + 1) % 3 = 2 := by
    intro m
    induction m with
    | zero => decide
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · -- 2^(2(n+1)) = 2^(2n+1) * 2
        have he : 2 ^ (2 * (n + 1)) = 2 ^ (2 * n + 1) * 2 := by
          rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega, Nat.pow_add]
          rw [Nat.pow_one]
        rw [he, Nat.mul_mod]
        omega
      · -- 2^(2(n+1)+1) = 2^(2n+1) * 4
        have he : 2 ^ (2 * (n + 1) + 1) = 2 ^ (2 * n + 1) * 4 := by
          rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by omega, Nat.pow_add]
          rw [show (2 : Nat) ^ 2 = 4 from by decide]
        rw [he, Nat.mul_mod]
        omega
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, rfl⟩ := he
    have := (key m).1
    omega
  · obtain ⟨m, rfl⟩ := ho
    have := (key m).2
    omega

/-- The coloring is well-defined on residue classes. -/
theorem color_eq_iff {x y : Nat} : color x = color y ↔ x % 3 = y % 3 := by
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.val_injective h

/-- The 3-coloring avoids every difference that is a power of two. -/
theorem coloring_avoids_S : ∀ x y : Nat, Nat.dist x y ∈ S → color x ≠ color y := by
  intro x y hxy
  obtain ⟨k, hk⟩ := hxy
  have hdist : Nat.dist x y = 2 ^ k := hk
  intro hcon
  have hmod : x % 3 = y % 3 := color_eq_iff.mp hcon
  rcases Nat.lt_or_ge x y with hlt | hge
  · have h1 : Nat.dist x y = y - x := by
      rw [Nat.dist_eq, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
      exact (Nat.zero_add _).symm
    have hyx : y - x = 2 ^ k := by omega
    have hy : y = x + 2 ^ k := by omega
    have hC : (x + 2 ^ k) % 3 = x % 3 := by omega
    rw [Nat.add_mod] at hC
    have hb : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by omega)
    have ha : x % 3 < 3 := Nat.mod_lt _ (by omega)
    have h0 : 2 ^ k % 3 = 0 := by omega
    exact two_pow_mod_three_ne_zero k h0
  · have h1 : Nat.dist x y = x - y := by
      rw [Nat.dist_eq, Nat.sub_eq_zero_of_le hge]
      exact (Nat.zero_add _).symm
    have hyx : x - y = 2 ^ k := by omega
    have hx : x = y + 2 ^ k := by omega
    have hC : (y + 2 ^ k) % 3 = y % 3 := by omega
    rw [Nat.add_mod] at hC
    have hb : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by omega)
    have ha : y % 3 < 3 := Nat.mod_lt _ (by omega)
    have h0 : 2 ^ k % 3 = 0 := by omega
    exact two_pow_mod_three_ne_zero k h0

/-- The squaring map `k ↦ 2^k` is injective (elementary core argument). -/
theorem pow_two_injective : Function.Injective (fun k : Nat => 2 ^ k) := by
  intro a b hab
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hab (by
      have := Nat.pow_lt_pow_right (by decide) h
      omega)
  · exact h
  · exact absurd hab (by
      have := Nat.pow_lt_pow_right (by decide) h
      omega)

/-- `S` is infinite. -/
theorem S_infinite : S.Infinite :=
  Set.infinite_range_of_injective pow_two_injective

/-- Density zero: at most `log₂ N + 1` elements of `S` lie in `[1, N]`. -/
theorem density : ∀ N : Nat, (S ∩ Set.Icc 1 N).ncard ≤ Nat.log2 N + 1 := by
  intro N
  have hsub : (S ∩ Set.Icc 1 N) ⊆ (Set.Icc 0 (Nat.log2 N)).image (fun k : Nat => 2 ^ k) := by
    rintro x ⟨⟨k, rfl⟩, h1, hN⟩
    refine Set.mem_image_of_mem _ ?_
    exact (Nat.le_log2 (by omega)).mpr hN
  calc (S ∩ Set.Icc 1 N).ncard
      ≤ ((Set.Icc 0 (Nat.log2 N)).image (fun k : Nat => 2 ^ k)).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (Set.Icc 0 (Nat.log2 N)).ncard := Set.ncard_image_le _
    _ ≤ ((Finset.range (Nat.log2 N + 1) : Set Nat)).ncard :=
        Set.ncard_le_ncard (by
          intro k hk
          exact Finset.mem_range.mpr (by omega))
    _ = Nat.log2 N + 1 := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- The complete affirmative answer for the powers of two: an infinite,
density-zero set of differences together with a 3-coloring avoiding it. -/
theorem jsp_000745 :
    S.Infinite ∧
    (∀ N : Nat, (S ∩ Set.Icc 1 N).ncard ≤ Nat.log2 N + 1) ∧
    ∀ x y : Nat, Nat.dist x y ∈ S → color x ≠ color y :=
  ⟨S_infinite, density, coloring_avoids_S⟩

end JSP000745
