/-
Copyright (c) 2026 Justin Sun Prize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-000415: Covering the vertices of an edge-colored complete graph by few monochromatic paths

Erdős and Gyárfás asked whether the vertices of every `r`-coloring of the
complete graph `K_n` can be covered by `f(n, r)` monochromatic paths with
`f(n, r) = o(log n)`; the answer is yes, with the sharp asymptotics settled
in 2024 (arXiv:2409.03623).  The 2-color case is the classical
Gerencsér–Gyárfás theorem (1967).

We formalize the base case of the Gerencsér–Gyárfás phenomenon: in every
2-coloring of the edges of `K_3`, the *whole vertex set* can be covered by a
single monochromatic path of length 2.  Indeed, of the three edges, two have
the same color, and any two edges of a triangle share a vertex, so they form
a monochromatic 3-vertex path.

The file is deliberately import-free.
-/

namespace JSP000415

/-- The bounded-case statement: for the 2-colored complete graph on three
vertices `{0, 1, 2}`, some color `c` and some three *distinct* vertices
`a b d` have both edges `a—b` and `b—d` colored `c`, hence the monochromatic
path `a—b—d` covers every vertex of the graph. -/
theorem one_monochromatic_path_covers_K3 :
    ∀ (G : Fin 3 → Fin 3 → Bool),
      (∀ a b : Fin 3, G a b = G b a) →
      ∃ (c : Bool) (a b d : Fin 3),
        a ≠ b ∧ b ≠ d ∧ a ≠ d ∧
        G a b = c ∧ G b d = c ∧ ∀ v : Fin 3, v = a ∨ v = b ∨ v = d := by
  intro G hsym
  by_cases h1 : G 0 1 = G 0 2
  · -- edges 0—1 and 0—2 share the color `G 0 1`; path 1—0—2
    refine ⟨G 0 1, 1, 0, 2, by decide, by decide, by decide, ?_, ?_, by decide⟩
    · rw [hsym 1 0]
    · exact h1.symm
  · by_cases h2 : G 1 2 = G 0 1
    · -- edges 0—1 and 1—2 share the color `G 0 1`; path 0—1—2
      refine ⟨G 0 1, 0, 1, 2, by decide, by decide, by decide, rfl, h2, by decide⟩
    · -- the three colors cannot be pairwise distinct (only two colors!)
      -- so `G 1 2 = G 0 2`, and edges 0—2 and 2—1 form the path 0—2—1
      have h12 : G 1 2 = G 0 2 := by
        cases h01 : G 0 1 <;> cases h02 : G 0 2 <;> cases h122 : G 1 2 <;> simp_all
      refine ⟨G 0 2, 0, 2, 1, by decide, by decide, by decide, rfl, ?_, by decide⟩
      rw [hsym 2 1]
      exact h12

end JSP000415
