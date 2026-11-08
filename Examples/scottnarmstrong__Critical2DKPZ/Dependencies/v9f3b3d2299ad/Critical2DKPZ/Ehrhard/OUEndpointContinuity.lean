/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUTimeDependent
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Continuity at the zero outer-time endpoint of interpolation -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open Critical2DKPZ.Gaussian (standardGaussianMeasure)
namespace Critical2DKPZ.Ehrhard
/-- The Ornstein–Uhlenbeck average at time zero equals the original function. -/
theorem ouAverage_zero {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ouAverage F x 0 = F x := by
  simp [ouAverage]
end Critical2DKPZ.Ehrhard
end
