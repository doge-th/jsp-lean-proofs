/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Basic

/-!
# JSP-000493 — Possible numbers of determined lines of a 4-point set

For planar point sets of a prescribed size, which total numbers of determined
(lines) are possible?  For four points we exhibit all three possibilities
over configurations with integer coordinates:

* `1` determined line — four collinear points;
* `4` determined lines — three collinear points plus one off the line;
* `6` determined lines — four points in general position (no three collinear).

Lines are represented by normalized integer triples `(a, b, c)` with the line
`a*x + b*y = c` and `(a, b)` primitive with canonical sign.
-/

namespace Mega5.JSP000493

/-- Normalized integer equation of the line through two distinct points. -/
def normLine (p q : ℤ × ℤ) : ℤ × ℤ × ℤ :=
  let a : ℤ := p.2 - q.2
  let b : ℤ := q.1 - p.1
  let g : ℕ := Nat.gcd a.natAbs b.natAbs
  let a' : ℤ := a / (g : ℤ)
  let b' : ℤ := b / (g : ℤ)
  let c' : ℤ := a' * p.1 + b' * p.2
  if a' < 0 ∨ (a' = 0 ∧ b' < 0) then (-(a'), -(b'), -(c')) else (a', b', c')

/-- All determined lines of a point set (image over pairs `i < j`). -/
def determined (pts : List (ℤ × ℤ)) : List (ℤ × ℤ × ℤ) :=
  (List.range pts.length).flatMap
    (fun i => (List.range pts.length).filterMap
      (fun j => if i < j then some (normLine (pts.getD i 0) (pts.getD j 0))
                else none))

/-- Deduplicate a list. -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | a :: t => let r := dedup t; if r.contains a then r else a :: r

/-- Number of determined lines of a 4-point set. -/
abbrev dcount (pts : List (ℤ × ℤ)) : ℕ := (dedup (determined pts)).length

/-- Collinearity of three points (zero signed area). -/
abbrev collinear (a b c : ℤ × ℤ) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

/-- Four collinear points determine exactly one line. -/
theorem four_collinear_one_line : dcount [(0, 0), (1, 0), (2, 0), (3, 0)] = 1 := by
  native_decide

/-- Three collinear points plus one off the line determine exactly four lines. -/
theorem three_plus_one : dcount [(0, 0), (1, 0), (2, 0), (0, 1)] = 4 := by
  native_decide

/-- The general-position configuration. -/
abbrev gp4 : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, 1)]

/-- Four points in general position determine exactly six lines, and no three
    of them are collinear. -/
theorem general_position :
    dcount gp4 = 6 ∧
    ∀ i j k : Fin 4, i ≠ j → j ≠ k → i ≠ k →
      ¬ collinear (gp4.getD i.val (0, 0)) (gp4.getD j.val (0, 0))
        (gp4.getD k.val (0, 0)) := by
  native_decide

/-- All three totals occur for 4-point configurations. -/
theorem possible_totals :
    dcount [(0, 0), (1, 0), (2, 0), (3, 0)] = 1 ∧
    dcount [(0, 0), (1, 0), (2, 0), (0, 1)] = 4 ∧
    dcount gp4 = 6 :=
  ⟨four_collinear_one_line, three_plus_one, general_position.1⟩

end Mega5.JSP000493
