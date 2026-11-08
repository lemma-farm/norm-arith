/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.gaussianCovariance`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- The mixed second moment of centered square-integrable real random variables; it is their
covariance under those centering hypotheses. All uses below supply centering and `L²`, so the
Bochner integral is genuine. See [KRV, Theorem 12.1]. -/
noncomputable def gaussianCovariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y Z : Ω → ℝ) : ℝ :=
  ∫ ω, Y ω * Z ω ∂P
end DOZZ
