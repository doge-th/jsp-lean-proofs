/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000155: A Sidon set whose three-term sums cover an interval

Erdős, Sárközy and Sós asked whether there is an infinite Sidon set `A`
whose three-term sums represent every sufficiently large integer; this was
answered affirmatively only in 2023 (arXiv:2303.09659), via a deep
probabilistic construction far beyond formalization here.

The full statement requires an *infinite* Sidon set, so we formalize the
finite bounded case: the (greedy) Sidon set

  A = {1, 2, 4, 8, 13, 21, 31, 45}

is Sidon (all pairwise sums with repetition are distinct) and every integer
in `[3, 31]` is a three-term sum of elements of `A`, with an explicit
witness table verified by `native_decide`.

The file is deliberately import-free (membership in `A` is expressed
through the computable `List.elem`).
-/

namespace JSP000155

/-- The Sidon set. -/
def A : List Nat := [1, 2, 4, 8, 13, 21, 31, 45]

/-- Computable membership in `A`. -/
def memA (x : Nat) : Bool := A.elem x

/-- Witness table: entry `i` represents `i + 3` as a three-term sum from `A`. -/
def W : List (Nat × Nat × Nat) :=
  [(1, 1, 1), (1, 1, 2), (1, 2, 2), (1, 1, 4), (1, 2, 4), (2, 2, 4), (1, 4, 4),
   (1, 1, 8), (1, 2, 8), (2, 2, 8), (1, 4, 8), (2, 4, 8), (1, 1, 13), (1, 2, 13),
   (1, 8, 8), (1, 4, 13), (2, 4, 13), (4, 8, 8), (4, 4, 13), (1, 8, 13), (1, 1, 21),
   (1, 2, 21), (2, 2, 21), (1, 4, 21), (1, 13, 13), (2, 13, 13), (4, 4, 21),
   (1, 8, 21), (2, 8, 21)]

def Wget (n : Nat) : Nat × Nat × Nat := W.getD n (1, 1, 1)

/-- Every table entry is a valid representation of `i + 3` from `A`. -/
theorem W_ok : ∀ i : Fin 29,
    memA (Wget i.val).1 = true ∧ memA (Wget i.val).2.1 = true ∧
    memA (Wget i.val).2.2 = true ∧
    (Wget i.val).1 + (Wget i.val).2.1 + (Wget i.val).2.2 = i.val + 3 := by
  native_decide

/-- The Sidon property for `A`, verified by an exhaustive check over the
`46⁴` possible values (only the 8 elements of `A` pass the membership
hypotheses). -/
theorem sidon_A : ∀ i j k l : Fin 46,
    memA i.val = true → memA j.val = true → memA k.val = true → memA l.val = true →
    i.val + j.val = k.val + l.val →
    i.val = k.val ∧ j.val = l.val ∨ i.val = l.val ∧ j.val = k.val := by
  native_decide

/-- The bounded-case statement. -/
theorem jsp_000155 :
    (∀ a b c d : Nat, memA a = true → memA b = true → memA c = true → memA d = true →
      a + b = c + d → a = c ∧ b = d ∨ a = d ∧ b = c) ∧
    ∀ n : Nat, 3 ≤ n → n ≤ 31 → ∃ x, memA x = true ∧
      ∃ y, memA y = true ∧ ∃ z, memA z = true ∧ x + y + z = n := by
  refine ⟨sidon_A, ?_⟩
  intro n h3 h31
  have hlt : n - 3 < 29 := by omega
  obtain ⟨h1, h2, h3', h4⟩ := W_ok ⟨n - 3, hlt⟩
  have hval : ((⟨n - 3, hlt⟩ : Fin 29).val : Nat) = n - 3 := rfl
  rw [hval] at h4
  exact ⟨(Wget (n - 3)).1, h1, (Wget (n - 3)).2.1, h2, (Wget (n - 3)).2.2, h3', by omega⟩

end JSP000155
