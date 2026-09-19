/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-!
# JSP-000444 — Three-color Ramsey number R(3,3,3)

How fast does the three-color Ramsey number grow for triangles in the first
two colors versus a large clique in the third?  The base case of the growth is
the classical Greenwood–Gleason value `R(3,3,3) = 17`.

We formalize both bounds:

* Lower bound (existence): the Greenwood–Gleason 3-coloring of `K16` with no
  monochromatic triangle.  Vertices are the elements of `Fin 16 = GF(2)^4`;
  the color of edge `xy` is `cls (x ^^^ y)`, where `cls` partitions
  `GF(16) \ {0}` into the three xor-sum-free classes
  `{1,8,10,12,15}`, `{2,3,7,11,13}`, `{4,5,6,9,14}`.
* Upper bound: every 3-coloring of the edges of `K17` contains a
  monochromatic triangle, proved by hand via the standard pigeonhole
  argument and a two-color triangle lemma.
-/

namespace Mega5.JSP000444

/-! ### The Greenwood-Gleason coloring (lower bound) -/

/-- The three xor-sum-free classes of `GF(16) \ {0}` (discrete log base `2`
    modulo `3` for `x^4 + x + 1`); `0 ↦ 3` as a garbage value. -/
def cls : ℕ → ℕ
  | 1 => 0 | 8 => 0 | 10 => 0 | 12 => 0 | 15 => 0
  | 2 => 1 | 3 => 1 | 7 => 1 | 11 => 1 | 13 => 1
  | 4 => 2 | 5 => 2 | 6 => 2 | 9 => 2 | 14 => 2
  | _ => 3

/-- Each class is xor-sum-free: distinct nonzero `a`, `b` of one class never
    have `a ^^^ b` in the same class (verified over all 256 pairs). -/
theorem cls_sum_free :
    ∀ a b : Fin 16, a.val ≠ 0 → b.val ≠ 0 → a ≠ b →
      cls a.val = cls b.val → cls (Nat.xor a.val b.val) ≠ cls a.val := by
  native_decide

/-- The Greenwood–Gleason coloring of `K16` has no monochromatic triangle
    (verified over all `16^3` vertex triples). -/
theorem greenwood_gleason :
    ∀ x y z : Fin 16, x ≠ y → y ≠ z → x ≠ z →
      ¬ (cls (Nat.xor x.val y.val) = cls (Nat.xor y.val z.val) ∧
         cls (Nat.xor y.val z.val) = cls (Nat.xor x.val z.val)) := by
  native_decide

/-! ### Small helper lemmas about `Fin 3` -/

/-- Trichotomy in `Fin 3`. -/
theorem fin3_trichotomy (v : Fin 3) : (v ≠ 0 ∧ v ≠ 1) ↔ v = 2 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : v.val ≠ 0 := fun h => h1 (Fin.val_inj.mp h)
    have h2' : v.val ≠ 1 := fun h => h2 (Fin.val_inj.mp h)
    have hv : v.val < 3 := v.isLt
    have h2v : (2 : Fin 3).val = 2 := rfl
    exact Fin.val_inj.mp (by omega)
  · intro h
    rw [h]
    exact ⟨by decide, by decide⟩

/-- The third color. -/
theorem fin3_third (k v : Fin 3) : v ≠ k → v ≠ k + 1 → v = k + 2 := by
  intro h1 h2
  have h1' : v.val ≠ k.val := fun h => h1 (Fin.val_inj.mp h)
  have h2' : v.val ≠ (k + 1).val := fun h => h2 (Fin.val_inj.mp h)
  have e : (k + 1).val = (k.val + 1) % 3 := rfl
  have e2 : (k + 2).val = (k.val + 2) % 3 := rfl
  have hk : k.val < 3 := k.isLt
  have hv : v.val < 3 := v.isLt
  exact Fin.val_inj.mp (by omega)

/-! ### Finset lemmas -/

/-- The second color is not the first. -/
theorem fin3_one_ne_zero (v : Fin 3) (h : v = 1) : v ≠ 0 := by
  rw [h]
  exact Fin.zero_ne_one.symm

/-- The second color is not the third. -/
theorem fin3_one_ne_two (v : Fin 3) (h : v = 1) : v ≠ 2 := by
  rw [h]
  decide

/-- Splitting a cardinality along a decidable predicate. -/
private theorem card_filter_split {α : Type*} [DecidableEq α] (u : Finset α)
    (p : α → Prop) [DecidablePred p] :
    u.card = (u.filter p).card + (u.filter fun x => ¬ p x).card := by
  induction u using Finset.induction with
  | empty => simp
  | insert a u h ih =>
    have hf1 : a ∉ u.filter p := fun hm => h ((Finset.mem_filter.mp hm).1)
    have hf2 : a ∉ u.filter fun x => ¬ p x := fun hm => h ((Finset.mem_filter.mp hm).1)
    rw [Finset.filter_insert]
    split
    · next hpa =>
        simp [hpa, h, hf1, hf2, ih, Finset.filter_insert,
          Finset.card_insert_of_notMem] <;> omega
    · next hpa =>
        simp [hpa, h, hf1, hf2, ih, Finset.filter_insert,
          Finset.card_insert_of_notMem] <;> omega

/-- Three distinct elements of a set of size at least three. -/
private theorem exists_three_of_card {α : Type*} [DecidableEq α] {u : Finset α}
    (h3 : 3 ≤ u.card) :
    ∃ b ∈ u, ∃ d ∈ u, ∃ e ∈ u, b ≠ d ∧ d ≠ e ∧ b ≠ e := by
  have hnz : ∃ b, b ∈ u := by
    by_contra hn
    rw [not_exists] at hn
    have h0 : u.card = 0 := Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr hn)
    omega
  obtain ⟨b, hb⟩ := hnz
  have h2 : 2 ≤ (u.erase b).card := by
    have hc := Finset.card_erase_of_mem hb
    omega
  have hnz2 : ∃ d, d ∈ u.erase b := by
    by_contra hn
    rw [not_exists] at hn
    have h0 : (u.erase b).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr hn)
    omega
  obtain ⟨d, hd⟩ := hnz2
  have h1 : 1 ≤ ((u.erase b).erase d).card := by
    have h5 := Finset.card_erase_of_mem hd
    have h6 := Finset.card_erase_of_mem hb
    omega
  have hnz3 : ∃ e, e ∈ (u.erase b).erase d := by
    by_contra hn
    rw [not_exists] at hn
    have h0 : ((u.erase b).erase d).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr hn)
    omega
  obtain ⟨e, he⟩ := hnz3
  have hb1 : d ≠ b := Finset.ne_of_mem_erase hd
  have hb2 : e ≠ d := Finset.ne_of_mem_erase he
  have he2 : e ∈ u.erase b := (Finset.mem_erase.mp he).2
  have hb3 : e ≠ b := Finset.ne_of_mem_erase he2
  exact ⟨b, hb, d, (Finset.mem_erase.mp hd).2, e, (Finset.mem_erase.mp he2).2,
    hb1.symm, hb2.symm, hb3.symm⟩

/-- Two-color triangle lemma, color-blind form: in any `Bool`-coloring of the
    pairs of a set of at least six elements there are three distinct elements
    whose three pair-values coincide. -/
private theorem exists_equal_triple {α : Type*} [DecidableEq α]
    (s : Finset α) (g : α → α → Bool) (h6 : 6 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ d ∈ s, a ≠ b ∧ b ≠ d ∧ a ≠ d ∧
      g a b = g b d ∧ g b d = g a d := by
  have hnz : ∃ a, a ∈ s := by
    by_contra hn
    rw [not_exists] at hn
    have h0 : s.card = 0 := Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr hn)
    omega
  obtain ⟨a, ha⟩ := hnz
  have h5 : 5 ≤ (s.erase a).card := by
    have hc := Finset.card_erase_of_mem ha
    omega
  -- split the other five vertices by the color of their edge to `a`
  have hsplit := card_filter_split (s.erase a) (fun x => g a x = true)
  -- auxiliary: a set of at least three vertices all joined to `a` in one
  -- color yields the desired equal triple
  have key : ∀ T : Finset α, 3 ≤ T.card →
      (∀ x ∈ T, x ∈ s ∧ x ≠ a) → (∀ x ∈ T, g a x = true) ∨ (∀ x ∈ T, g a x = false) →
      ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
        g p q = g q r ∧ g q r = g p r := by
    intro T h3T hmem hcol
    obtain ⟨x, hx, y, hy, z, hz, hxyd, hyzd, hxzd⟩ := exists_three_of_card h3T
    have hxs : x ∈ s ∧ x ≠ a := hmem x hx
    have hys : y ∈ s ∧ y ≠ a := hmem y hy
    have hzs : z ∈ s ∧ z ≠ a := hmem z hz
    rcases hcol with hT | hT
    · cases hxy : g x y with
      | true =>
        exact ⟨a, ha, x, hxs.1, y, hys.1, hxs.2.symm, hxyd, hys.2.symm,
          by rw [hT x hx, hxy], by rw [hxy, hT y hy]⟩
      | false =>
        cases hxz : g x z with
        | true =>
          exact ⟨a, ha, x, hxs.1, z, hzs.1, hxs.2.symm, hxzd, hzs.2.symm,
            by rw [hT x hx, hxz], by rw [hxz, hT z hz]⟩
        | false =>
          cases hyz : g y z with
          | true =>
            exact ⟨a, ha, y, hys.1, z, hzs.1, hys.2.symm, hyzd, hzs.2.symm,
              by rw [hT y hy, hyz], by rw [hyz, hT z hz]⟩
          | false =>
            exact ⟨x, hxs.1, y, hys.1, z, hzs.1, hxyd, hyzd, hxzd,
              by rw [hxy, hyz], by rw [hyz, hxz]⟩
    · cases hxy : g x y with
      | false =>
        exact ⟨a, ha, x, hxs.1, y, hys.1, hxs.2.symm, hxyd, hys.2.symm,
          by rw [hT x hx, hxy], by rw [hxy, hT y hy]⟩
      | true =>
        cases hxz : g x z with
        | false =>
          exact ⟨a, ha, x, hxs.1, z, hzs.1, hxs.2.symm, hxzd, hzs.2.symm,
            by rw [hT x hx, hxz], by rw [hxz, hT z hz]⟩
        | true =>
          cases hyz : g y z with
          | false =>
            exact ⟨a, ha, y, hys.1, z, hzs.1, hys.2.symm, hyzd, hzs.2.symm,
              by rw [hT y hy, hyz], by rw [hyz, hT z hz]⟩
          | true =>
            exact ⟨x, hxs.1, y, hys.1, z, hzs.1, hxyd, hyzd, hxzd,
              by rw [hxy, hyz], by rw [hyz, hxz]⟩
  have hmem1 : ∀ x ∈ (s.erase a).filter (fun x => g a x = true), x ∈ s ∧ x ≠ a := by
    intro x hx
    have h2 := (Finset.mem_filter.mp hx).1
    exact ⟨Finset.mem_of_mem_erase h2, Finset.ne_of_mem_erase h2⟩
  have hcol1 : ∀ x ∈ (s.erase a).filter (fun x => g a x = true), g a x = true := fun x hx =>
    (Finset.mem_filter.mp hx).2
  have hmem0 : ∀ x ∈ (s.erase a).filter (fun x => ¬ (g a x = true)), x ∈ s ∧ x ≠ a := by
    intro x hx
    have h2 := (Finset.mem_filter.mp hx).1
    exact ⟨Finset.mem_of_mem_erase h2, Finset.ne_of_mem_erase h2⟩
  have hcol0 : ∀ x ∈ (s.erase a).filter (fun x => ¬ (g a x = true)), g a x = false := by
    intro x hx
    have h2 := (Finset.mem_filter.mp hx).2
    cases h : g a x
    · rfl
    · exact absurd h h2
  by_cases h3T1 : 3 ≤ ((s.erase a).filter (fun x => g a x = true)).card
  · exact key _ h3T1 hmem1 (Or.inl hcol1)
  · have h3T0 : 3 ≤ ((s.erase a).filter (fun x => ¬ (g a x = true))).card := by
      have hle : ((s.erase a).filter (fun x => g a x = true)).card < 3 :=
        Nat.lt_of_not_ge h3T1
      omega
    exact key _ h3T0 hmem0 (Or.inr hcol0)

/-- **Upper bound**: every coloring of the pairs of `Fin 17` in three colors
    contains a monochromatic triangle, i.e. `R(3,3,3) ≤ 17`. -/
theorem r333_upper (c : Fin 17 → Fin 17 → Fin 3) :
    ∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      c x y = c y z ∧ c y z = c x z := by
  -- the 16 neighbors of vertex 0
  set N := Finset.univ.erase (0 : Fin 17) with hN
  have hNc : N.card = 16 := by
    rw [hN]
    have h1 := Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 17))
    have h2 : (Finset.univ : Finset (Fin 17)).card = 17 := by
      native_decide
    omega
  -- split the neighbors into the three color classes
  have e1 := card_filter_split N (fun x => c 0 x = 0)
  have e2 := card_filter_split (N.filter fun x => c 0 x ≠ 0) (fun x => c 0 x = 1)
  have hA1 : (N.filter fun x => c 0 x ≠ 0).filter (fun x => c 0 x = 1)
      = N.filter (fun x => c 0 x = 1) := by
    apply Finset.ext
    intro x
    constructor
    · intro hh
      have hm := Finset.mem_filter.mp hh
      have hxN : x ∈ N := (Finset.mem_filter.mp hm.1).1
      rw [hN] at hxN
      have hm2 := Finset.mem_erase.mp hxN
      exact Finset.mem_filter.mpr ⟨hm2.1, hm.2⟩
    · intro hh
      have hxN : x ∈ N := by
        rw [hN]
        exact Finset.mem_erase.mpr ⟨hh.1, Finset.mem_univ x⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hxN, fin3_one_ne_zero (c 0 x) hh.2⟩, hh.2⟩
  have hA2 : (N.filter fun x => c 0 x ≠ 0).filter (fun x => ¬ (c 0 x = 1))
      = N.filter (fun x => c 0 x = 2) := by
    apply Finset.ext
    intro x
    constructor
    · intro hh
      have hm := Finset.mem_filter.mp hh
      have hxN : x ∈ N := (Finset.mem_filter.mp hm.1).1
      rw [hN] at hxN
      have hm0 := Finset.mem_filter.mp hxN
      have hm2 := Finset.mem_erase.mp hm0.1
      have h2 := fin3_trichotomy (c 0 x) |>.mp ⟨hm0.2, hm.2⟩
      exact Finset.mem_filter.mpr ⟨hm2.1, h2⟩
    · intro hh
      have h2 := fin3_trichotomy (c 0 x) |>.mpr hh
      have hxN : x ∈ N := by
        rw [hN]
        exact Finset.mem_erase.mpr ⟨h2.1, Finset.mem_univ x⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hxN, h2.2⟩, h2.2⟩
  rw [hA1, hA2] at e2
  have hsplit : N.card = (N.filter fun x => c 0 x = 0).card
      + (N.filter fun x => c 0 x = 1).card + (N.filter fun x => c 0 x = 2).card := by
    omega
  -- pigeonhole: one class contains at least 6 neighbors
  have hex : ∃ k : Fin 3, 6 ≤ (N.filter fun x => c 0 x = k).card := by
    by_contra hc
    rw [not_exists] at hc
    have hle : ∀ k : Fin 3, (N.filter fun x => c 0 x = k).card ≤ 5 :=
      fun k => Nat.le_of_not_gt (fun h => hc k h)
    have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    omega
  obtain ⟨k, hk⟩ := hex
  by_cases hred : ∃ x ∈ N.filter (fun x => c 0 x = k),
      ∃ y ∈ N.filter (fun x => c 0 x = k), x ≠ y ∧ c x y = k
  · -- a class-colored edge closes a class-colored triangle with vertex 0
    obtain ⟨x, hx, y, hy, hxy, hcy⟩ := hred
    have hx' : x ∈ N := (Finset.mem_filter.mp hx).1
    have hy' : y ∈ N := (Finset.mem_filter.mp hy).1
    have hx0 : c 0 x = k := (Finset.mem_filter.mp hx).2
    have hy0 : c 0 y = k := (Finset.mem_filter.mp hy).2
    have hxn : x ≠ 0 := Finset.ne_of_mem_erase hx'
    have hyn : y ≠ 0 := Finset.ne_of_mem_erase hy'
    refine ⟨(0 : Fin 17), x, y, hxn, hxy, hyn, ?_, ?_⟩
    · rw [hx0, hcy]
    · rw [hcy, hy0]
  · -- no class-colored edge: the pairs carry the two other colors
    have hnk : ∀ x ∈ N.filter (fun x => c 0 x = k),
        ∀ y ∈ N.filter (fun x => c 0 x = k), x ≠ y → c x y ≠ k := by
      intro x hx y hy hne h
      exact hred ⟨x, hx, y, hy, hne, h⟩
    obtain ⟨a, ha, b, hb, d, hd, hab, hbd, had, he1, he2⟩ :=
      exists_equal_triple (N.filter fun x => c 0 x = k)
        (fun x y => decide (c x y = k + 1)) hk
    have e1' : (c a b = k + 1) ↔ (c b d = k + 1) := decide_eq_decide.mp he1
    have e2' : (c b d = k + 1) ↔ (c a d = k + 1) := decide_eq_decide.mp he2
    have haN : a ∈ N := (Finset.mem_filter.mp ha).1
    have hbN : b ∈ N := (Finset.mem_filter.mp hb).1
    have hdN : d ∈ N := (Finset.mem_filter.mp hd).1
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase haN
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hbN
    have hd0 : d ≠ 0 := Finset.ne_of_mem_erase hdN
    by_cases hv : c a b = k + 1
    · refine ⟨a, b, d, ha0, hbd, hb0, ?_, ?_⟩
      · exact e1'.mp hv
      · exact e2'.mp (e1'.mpr hv)
    · -- all three pair-values are the third color
      have hna : c a b ≠ k := hnk a ha b hb hab
      have hnb : c b d ≠ k := fun h => hv (e1'.mpr h)
      have hnd : c a d ≠ k := fun h => hv (e1'.mp (e2'.mpr h))
      have t1 : c a b = k + 2 := fin3_third k (c a b) hna hv
      have t2 : c b d = k + 2 := fin3_third k (c b d) hnb (fun h => hv (e1'.mp h))
      have t3 : c a d = k + 2 := fin3_third k (c a d) hnd (fun h => hv (e1'.mp (e2'.mp h)))
      exact ⟨a, b, d, ha0, hbd, had, by rw [t1, t2], by rw [t2, t3]⟩

end Mega5.JSP000444
