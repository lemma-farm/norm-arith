-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SymmetricGaussianRealization
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianSpectralNorm
set_option autoImplicit false
/-! The manuscript's literal trace-variance hypothesis supplies the proved
Gaussian realization, including singular covariance and almost-sure symmetry. -/
@[expose] public section
namespace SlowEquilibration.SymmetricGaussianCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge SymmetricGaussianRealization
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {m : ℕ}
end
end SlowEquilibration.SymmetricGaussianCovariance
