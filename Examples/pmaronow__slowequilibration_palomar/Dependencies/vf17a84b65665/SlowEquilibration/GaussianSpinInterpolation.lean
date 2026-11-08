-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphericalConcentration
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
set_option autoImplicit false
@[expose] public section
/-! Ordinary integral partition functions for bounded measurable families of
linear fields. The spin measure may be nonatomic, including the genuine
uniform sphere law. Differentiation is proved by dominated convergence. -/
namespace SlowEquilibration.GaussianSpinInterpolation
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
variable {V H : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
end
end SlowEquilibration.GaussianSpinInterpolation
