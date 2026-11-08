-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianLocalCoordinates
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
set_option autoImplicit false
/-!
# Global Euclidean full-coefficient marked Gaussian Kac--Rice

A countable open cover is constructed from actual observation surjectivity.
Its disjoint Borel partition glues the independently proved canonical local
formula, preserving arbitrary full-coefficient Borel marks and infinite sums.
-/
@[expose] public section
namespace SlowEquilibration.GaussianLocalCoordinates
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianRegression
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
end
end SlowEquilibration.GaussianLocalCoordinates
