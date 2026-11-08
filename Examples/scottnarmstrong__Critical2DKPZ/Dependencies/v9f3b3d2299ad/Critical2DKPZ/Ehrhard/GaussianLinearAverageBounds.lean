/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.GaussianLinearAverage
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Uniform bounds for averages of bounded smooth Gaussian observables -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open Critical2DKPZ.Gaussian (standardGaussianMeasure)
namespace Critical2DKPZ.Ehrhard
/-- A uniform absolute bound is preserved by Gaussian linear averaging. -/
theorem abs_gaussianLinearAverage_le {E : Type*} {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (J : (Fin n → ℝ) → E → (Fin n → ℝ)) {C : ℝ} (hbound : ∀ y, |F y| ≤ C) (p : E) :
    |∫ z, F (J z p) ∂standardGaussianMeasure n| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (f := fun z => F (J z p)) (C := C)
    (ae_of_all (standardGaussianMeasure n) fun z => by
      simpa only [Real.norm_eq_abs] using hbound (J z p))
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end Critical2DKPZ.Ehrhard
end
