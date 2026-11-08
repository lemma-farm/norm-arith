-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GOEEdgeConcentration
set_option autoImplicit false
@[expose] public section
/-! Actual extremal eigenvalue convergence: outer confinement is supplemented
with the proved Jacobi edge approximation, rather than interpreted as inclusion. -/
namespace SlowEquilibration.GOEExtremalEdges
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
end
end SlowEquilibration.GOEExtremalEdges
