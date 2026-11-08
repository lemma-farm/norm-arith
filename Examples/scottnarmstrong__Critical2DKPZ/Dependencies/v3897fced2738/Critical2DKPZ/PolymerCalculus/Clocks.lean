/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.EvenCeil
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! For nonnegative times, the even ceiling has an error in `[0,2)` and rounded differences have a signed duration error of absolute value less than two. -/
@[expose] public section
namespace Critical2DKPZ
theorem evenCeil_mono : Monotone evenCeil := by
  intro s t h
  exact Nat.mul_le_mul_left 2 (Nat.ceil_mono (by linarith))
/-- A real number is bounded above by its even ceiling. -/
theorem le_evenCeil (t : ℝ) : t ≤ (evenCeil t : ℝ) := by
  have h := Nat.le_ceil (t / 2)
  simp only [evenCeil, Nat.cast_mul, Nat.cast_ofNat]
  linarith only [h]
/-- The even ceiling of a nonnegative number is less than that number plus two. -/
theorem evenCeil_lt_add_two {t : ℝ} (ht : 0 ≤ t) : (evenCeil t : ℝ) < t + 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ t / 2 by linarith)
  simp only [evenCeil, Nat.cast_mul, Nat.cast_ofNat]
  linarith only [h]
/-- The even ceiling of a nonnegative time exceeds it by a value in `[0,2)`. -/
theorem evenCeil_error {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (evenCeil t : ℝ) - t ∧ (evenCeil t : ℝ) - t < 2 := by
  constructor
  · linarith only [le_evenCeil t]
  · linarith only [evenCeil_lt_add_two ht]
/-- Two rounded endpoints have a signed duration error of absolute value below two. -/
theorem evenCeil_duration_error {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |((evenCeil t : ℝ) - evenCeil s) - (t - s)| < 2 := by
  obtain ⟨hs0, hs2⟩ := evenCeil_error hs
  obtain ⟨ht0, ht2⟩ := evenCeil_error ht
  rw [abs_lt]
  constructor <;> linarith only [hs0, hs2, ht0, ht2]
end Critical2DKPZ
