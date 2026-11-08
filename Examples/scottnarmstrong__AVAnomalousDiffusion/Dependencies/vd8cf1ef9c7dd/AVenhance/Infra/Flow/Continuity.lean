-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8cf1ef9c7dd.AVenhance.Statements.Flow.IsFlow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8cf1ef9c7dd.AVenhance.Infra.Flow.Estimates
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8cf1ef9c7dd.AVenhance.Infra.Flow.Laws
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Joint continuity follows from curve continuity, the flow law, and the
spatial Grönwall estimate. -/
@[expose] public section
open Homogenization
open Filter
open scoped Topology
namespace AVenhance.Infra.Flow
end AVenhance.Infra.Flow
