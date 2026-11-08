-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianSpinInterpolation
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
set_option autoImplicit false
@[expose] public section
namespace SlowEquilibration.GaussianSpinComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {ι V : Type*} [Fintype ι] [MeasurableSpace V]
variable [DecidableEq ι]
end
end SlowEquilibration.GaussianSpinComparison
