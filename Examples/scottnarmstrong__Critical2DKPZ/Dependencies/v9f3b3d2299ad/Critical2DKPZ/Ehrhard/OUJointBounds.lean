/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUJointRegularity
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUTimeDependent
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.GaussianLinearAverageBounds
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Bounds for space and time derivatives of bounded smooth OU inputs -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
namespace Critical2DKPZ.Ehrhard
/-- Ornstein–Uhlenbeck averaging preserves a uniform absolute bound. -/
theorem abs_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hF : ∀ y, |F y| ≤ B) (x : Fin n → ℝ) (t : ℝ) : |ouAverage F x t| ≤ B :=
  abs_gaussianLinearAverage_le
    (fun z y => Real.exp (-t) • y + Real.sqrt (1 - Real.exp (-2 * t)) • z) hF x
end Critical2DKPZ.Ehrhard
end
