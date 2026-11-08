-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianFiniteMaximum
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
set_option autoImplicit false
/-!
# Compact-index Gaussian supremum comparison

The compact feature image has deterministic finite operator-norm nets. Actual
Gaussian suprema are Lipschitz functions of the Gaussian input and have an
integrable Gaussian norm envelope. The finite Sudakov--Fernique comparison
therefore passes to the genuine compact supremum with a proved net error.
-/
@[expose] public section
namespace SlowEquilibration.GaussianCompactMaximum
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinComparison GaussianSpinInterpolation GaussianFiniteMaximum
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Nonempty V]
variable [TopologicalSpace V] [CompactSpace V]
end
end SlowEquilibration.GaussianCompactMaximum
