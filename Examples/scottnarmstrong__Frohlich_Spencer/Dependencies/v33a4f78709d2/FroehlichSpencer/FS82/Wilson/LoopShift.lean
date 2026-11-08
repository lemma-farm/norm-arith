/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v33a4f78709d2.FroehlichSpencer.FS82.Wilson.ShiftProfile
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The explicit loop shift on `ℤ⁴` and its energy

The explicit shift `α` has components along the axes 2 and 3 only,
`α_j(y) = a_{depth(y₀,y₁), j}(y₂, y₃)`, where `depth` is the distance of the column from the
boundary of the sheet and `a_d` is the transverse shift of `ShiftProfile`.

The main result is `loopEnergy_le`: the sum of the squares of the components of `σ - dα`
over any finite box is at most `6 (L + T)`.
-/
public section
namespace FroehlichSpencer.FS82.Wilson
open Finset
/-- The squared norm of the difference of two consecutive transverse shifts. -/
theorem sum_shift_diff_sq_le {d d' : ℕ} (h : d' = d ∨ d' = d + 1 ∨ d = d' + 1)
    (s t : Finset ℤ) :
    ∑ y ∈ s, ∑ z ∈ t, ((-(shiftTwo d' y z - shiftTwo d y z)) ^ 2 +
        (-(shiftThree d' y z - shiftThree d y z)) ^ 2) ≤
      if d' = d then 0 else levelBound (min d d') := by
  rcases h with h | h | h
  · subst h
    simp
  · subst h
    have hne : d + 1 ≠ d := by omega
    rw [ite_eq_right hne, min_eq_left (by omega : d ≤ d + 1)]
    refine le_trans (le_of_eq ?_) (sum_level_sq_le d s t)
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    rw [shiftTwo_succ, shiftThree_succ]
    ring
  · subst h
    have hne : d' ≠ d' + 1 := by omega
    rw [ite_eq_right hne, min_eq_right (by omega : d' ≤ d' + 1)]
    refine le_trans (le_of_eq ?_) (sum_level_sq_le d' s t)
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    rw [shiftTwo_succ, shiftThree_succ]
    ring
end FroehlichSpencer.FS82.Wilson
end
