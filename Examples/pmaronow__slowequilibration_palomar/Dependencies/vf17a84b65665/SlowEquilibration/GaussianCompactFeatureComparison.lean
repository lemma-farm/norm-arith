-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianCompactMaximum
public import Mathlib.Probability.ProductMeasure
set_option autoImplicit false
/-!
# Compact Gaussian comparison on independent coefficient spaces

The two actual coefficient spaces are joined by their genuine product Gaussian
law. Their increment norm comparison is exactly the signed covariance
comparison required by compact Sudakov--Fernique.
-/
@[expose] public section
namespace SlowEquilibration.GaussianCompactFeatureComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open GaussianSpinComparison GaussianSpinInterpolation GaussianCompactMaximum
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [TopologicalSpace V] [CompactSpace V] [Nonempty V]
end
end SlowEquilibration.GaussianCompactFeatureComparison
