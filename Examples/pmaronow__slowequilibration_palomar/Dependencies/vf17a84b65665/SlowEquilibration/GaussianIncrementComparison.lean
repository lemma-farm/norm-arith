-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianSpinComparison
set_option autoImplicit false
/-! Gaussian comparison from increment covariance, with arbitrary bounded
continuous or measurable spin features. No constant pointwise variance is
required. This is the finite-temperature Sudakov–Fernique comparison used for
covariance-dominated matrix fields. -/
@[expose] public section
namespace SlowEquilibration.GaussianSpinComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end
end SlowEquilibration.GaussianSpinComparison
