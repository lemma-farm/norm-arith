-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GOEEdgeConcentration
set_option autoImplicit false
/-! Actual rank-one Frobenius features for covariance-dominated Gaussian
symmetric matrices. The sharp increment bound compares their quadratic process
with a linear Gaussian process on the unit sphere. -/
@[expose] public section
namespace SlowEquilibration.GaussianMatrixFeatures
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
end
end SlowEquilibration.GaussianMatrixFeatures
