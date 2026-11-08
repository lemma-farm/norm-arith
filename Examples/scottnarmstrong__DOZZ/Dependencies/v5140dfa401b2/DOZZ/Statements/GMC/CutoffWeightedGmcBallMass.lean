/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v5140dfa401b2.DOZZ.Statements.GMC.GffRootCovariance
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.cutoffWeightedGmcBallMass`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- Cutoff weighted GMC mass with the distance singularity regularized at scale `δ`. See
[KRV, §7.2]. -/
noncomputable def cutoffWeightedGmcBallMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ α : ℝ) (z : ℂ)
    (R δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball z R,
    ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ∂
      regularizedGMC P Xc γ (Real.log (1 / δ)) ω
end DOZZ
