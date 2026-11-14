module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v33a4f78709d2.FroehlichSpencer.FS82.Wilson.ShiftProfile ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The transverse profile of the explicit loop shift

* `uni d` is the uniform weight `1/(d+1)` on `{0,…,d}` and `ramp d` is
  `j/((d+1)(d+2))` on `{1,…,d+1}`; `ramp d (j+1) - ramp d j = uni d j - uni (d+1) j`.
* `levelTwo d`, `levelThree d` are the two components of the level field `b_d` in the
  transverse `2–3` plane, with `curl b_d = u_d ⊗ u_d - u_{d+1} ⊗ u_{d+1}`.
* `shiftTwo d`, `shiftThree d` are the components of `a_d = Σ_{j<d} b_j`, with
  `curl a_d = u_0 ⊗ u_0 - u_d ⊗ u_d`: the unit flux of one plaquette is spread
  uniformly over the square `{0,…,d}²`.
* The squared norms are bounded over every finite index set, and the tent sums used for
  the perimeter bookkeeping are bounded.
-/
public section
namespace FroehlichSpencer.FS82.Wilson
open Finset
/-- `u_d`: the uniform weight `1/(d+1)` on `{0,…,d}`. -/
@[expose] noncomputable def uni (d : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (d : ℤ) then 1 / ((d : ℝ) + 1) else 0
/-- `X_d`: the ramp `j/((d+1)(d+2))` on `{1,…,d+1}`. -/
@[expose] noncomputable def ramp (d : ℕ) (j : ℤ) : ℝ :=
  if 1 ≤ j ∧ j ≤ (d : ℤ) + 1 then (j : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 2)) else 0

/-! ### Sums over arbitrary finite index sets -/

/-- The squared norm of the ramp, `(2d+3)/(6(d+1)(d+2))`. -/
@[expose] noncomputable def rampNormSq (d : ℕ) : ℝ :=
  (2 * (d : ℝ) + 3) / (6 * ((d : ℝ) + 1) * ((d : ℝ) + 2))

/-! ### The level field and the shift in the transverse plane -/
/-- Component along axis 2 of the level field `b_d`. -/
@[expose] noncomputable def levelTwo (d : ℕ) (y z : ℤ) : ℝ := -(uni (d + 1) y * ramp d z)
/-- Component along axis 3 of the level field `b_d`. -/
@[expose] noncomputable def levelThree (d : ℕ) (y z : ℤ) : ℝ := ramp d y * uni d z
/-- Component along axis 2 of `a_d = Σ_{j<d} b_j`. -/
@[expose] noncomputable def shiftTwo (d : ℕ) (y z : ℤ) : ℝ := ∑ j ∈ range d, levelTwo j y z
/-- Component along axis 3 of `a_d = Σ_{j<d} b_j`. -/
@[expose] noncomputable def shiftThree (d : ℕ) (y z : ℤ) : ℝ := ∑ j ∈ range d, levelThree j y z

@[expose] noncomputable def levelBound (d : ℕ) : ℝ :=
  (1 / 3) * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2)

/-! ### Series and tent sums -/
end FroehlichSpencer.FS82.Wilson
end

end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_a027a35d51d32abefd74_LoopShift ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
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
set_option linter.unusedVariables false in
/-- The squared norm of the difference of two consecutive transverse shifts. -/
theorem sum_shift_diff_sq_le {d d' : ℕ} (h : d' = d ∨ d' = d + 1 ∨ d = d' + 1)
    (s t : Finset ℤ) 
    (h_FroehlichSpencer_FS82_Wilson_sum_level_sq_le : ∀ (d : ℕ) (s t : Finset ℤ),
      ∑ y ∈ s,
          ∑ z ∈ t,
            (FroehlichSpencer.FS82.Wilson.levelTwo d y z ^ 2 +
              FroehlichSpencer.FS82.Wilson.levelThree d y z ^ 2) ≤
        FroehlichSpencer.FS82.Wilson.levelBound d)
    (h_FroehlichSpencer_FS82_Wilson_shiftTwo_succ : ∀ (d : ℕ) (y z : ℤ),
      FroehlichSpencer.FS82.Wilson.shiftTwo (d + 1) y z =
        FroehlichSpencer.FS82.Wilson.shiftTwo d y z + FroehlichSpencer.FS82.Wilson.levelTwo d y z)
    (h_FroehlichSpencer_FS82_Wilson_shiftThree_succ : ∀ (d : ℕ) (y z : ℤ),
      FroehlichSpencer.FS82.Wilson.shiftThree (d + 1) y z =
        FroehlichSpencer.FS82.Wilson.shiftThree d y z + FroehlichSpencer.FS82.Wilson.levelThree d y z)
    :
    ∑ y ∈ s, ∑ z ∈ t, ((-(shiftTwo d' y z - shiftTwo d y z)) ^ 2 +
        (-(shiftThree d' y z - shiftThree d y z)) ^ 2) ≤
      if d' = d then 0 else levelBound (min d d') := by
  rcases h with h | h | h
  · subst h
    simp
  · subst h
    have hne : d + 1 ≠ d := by omega
    rw [ite_eq_right hne, min_eq_left (by omega : d ≤ d + 1)]
    refine le_trans (le_of_eq ?_) (h_FroehlichSpencer_FS82_Wilson_sum_level_sq_le d s t)
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    rw [h_FroehlichSpencer_FS82_Wilson_shiftTwo_succ, h_FroehlichSpencer_FS82_Wilson_shiftThree_succ]
    ring
  · subst h
    have hne : d' ≠ d' + 1 := by omega
    rw [ite_eq_right hne, min_eq_right (by omega : d' ≤ d' + 1)]
    refine le_trans (le_of_eq ?_) (h_FroehlichSpencer_FS82_Wilson_sum_level_sq_le d' s t)
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    rw [h_FroehlichSpencer_FS82_Wilson_shiftTwo_succ, h_FroehlichSpencer_FS82_Wilson_shiftThree_succ]
    ring
end FroehlichSpencer.FS82.Wilson
end
