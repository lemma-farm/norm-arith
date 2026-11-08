-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianCompactFeatureComparison
public import Mathlib.Probability.Distributions.Gaussian.Fernique
set_option autoImplicit false
/-!
# Actual Gaussian norm second moment and expected norm bound
-/
@[expose] public section
namespace SlowEquilibration.GaussianNormMean
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (ι : Type*) [Fintype ι]
end
end SlowEquilibration.GaussianNormMean
