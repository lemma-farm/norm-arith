/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUFamily
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.FunctionalTimeDerivative
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The infinite-time endpoints of bounded Gaussian interpolation -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (standardGaussianMeasure)
open scoped Topology
namespace Critical2DKPZ.Ehrhard
theorem continuous_ouAverage_time {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) {B : ℝ} (hbound : ∀ z, |F z| ≤ B) (x : Fin n → ℝ) :
    Continuous (ouAverage F x) := by
  apply continuous_of_dominated (μ := standardGaussianMeasure n) (bound := fun _ => B)
  · intro t
    exact (hF.comp (by fun_prop)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound _
  · exact integrable_const B
  · exact ae_of_all _ fun z => hF.comp (by fun_prop)
end Critical2DKPZ.Ehrhard
end
