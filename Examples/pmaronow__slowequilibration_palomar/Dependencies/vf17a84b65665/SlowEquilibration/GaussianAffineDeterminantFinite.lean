module
-- SPDX-License-Identifier: Apache-2.0
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianAffineDeterminantUniform
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianDensity
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianNormMean
set_option autoImplicit false
@[expose] public section
/-! # Genuine Gaussian-ball bounds for the remaining finite dimensions -/
namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Set MeasureTheory ProbabilityTheory Filter Metric
open OAI.CriticalSK GOEAsymptotics SpectralTraceLipschitz
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
end
end SlowEquilibration.GaussianAffineDeterminant
