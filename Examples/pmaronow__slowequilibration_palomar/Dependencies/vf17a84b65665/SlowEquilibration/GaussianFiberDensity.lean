-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianRegressionDensity
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
set_option autoImplicit false
/-!
# Pointwise Gaussian regression on every affine observation fiber

The ambient ordinary Gaussian pdf is factored exactly on every specified fiber.
This proves the weighted fiber identity for arbitrary Borel marks at observation
zero without an almost-everywhere choice of a conditional density.
-/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace Topology ENNReal
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
end
end SlowEquilibration.GaussianRegression
