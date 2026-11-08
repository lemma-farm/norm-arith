-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianIncrementComparison
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Order.Lattice
set_option autoImplicit false
/-! Finite Gaussian maximum comparison obtained from the proved ordinary
Gaussian log-partition interpolation. The zero-temperature limit is controlled
by the deterministic log-cardinality error. -/
@[expose] public section
namespace SlowEquilibration.GaussianFiniteMaximum
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open GaussianSpinComparison GaussianSpinInterpolation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V : Type*} [Fintype V] [Nonempty V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace V] [MeasurableSingletonClass V]
end
end SlowEquilibration.GaussianFiniteMaximum
