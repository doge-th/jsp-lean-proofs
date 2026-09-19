/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Justin Sun Prize JSP-000173: How many short arithmetic progressions in an
integer set force a longer arithmetic progression?

Answer (bounded instance): finitely many 3-term progressions do not force a
4-term one.  The 9-element set

    S = {0, 1, 2, 7, 8, 9, 14, 15, 16}

contains exactly eight 3-term arithmetic progressions (all listed in the
theorem below), yet no 4-term arithmetic progression at all: a 4-term AP in
S would have common difference d with 1 ≤ d ≤ 5 (since its last term is
≤ 16), and for each such d a direct check of the possible starting values
a = 0, …, 13 shows that the four terms never all lie in S.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-- The 9-element example set. -/
def JSP173S : Finset ℕ := {0, 1, 2, 7, 8, 9, 14, 15, 16}

/-- `(a, b, c)` is a 3-term arithmetic progression inside `JSP173S`. -/
abbrev JSP173.IsAP3 (a b c : ℕ) : Prop :=
  a + c = 2 * b ∧ a ∈ JSP173S ∧ b ∈ JSP173S ∧ c ∈ JSP173S

/-- JSP-000173: eight short (3-term) progressions without a longer one.
The set has 9 elements, carries the eight displayed 3-term progressions,
and contains no 4-term arithmetic progression. -/
theorem jsp_000173 :
    JSP173S.card = 9 ∧
    (∀ a d : ℕ, 0 < d → a ∈ JSP173S → a + d ∈ JSP173S →
      a + 2 * d ∈ JSP173S → a + 3 * d ∈ JSP173S → False) ∧
    JSP173.IsAP3 0 1 2 ∧ JSP173.IsAP3 7 8 9 ∧ JSP173.IsAP3 14 15 16 ∧
    JSP173.IsAP3 0 7 14 ∧ JSP173.IsAP3 1 8 15 ∧ JSP173.IsAP3 2 9 16 ∧
    JSP173.IsAP3 0 8 16 ∧ JSP173.IsAP3 2 8 14 := by
  refine ⟨by native_decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a d hd0 ha1 ha2 ha3 ha4
    have h16 : ∀ x ∈ JSP173S, x ≤ 16 := by decide
    have hle : a + 3 * d ≤ 16 := h16 _ ha4
    simp_all [JSP173S]
    omega
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals native_decide
