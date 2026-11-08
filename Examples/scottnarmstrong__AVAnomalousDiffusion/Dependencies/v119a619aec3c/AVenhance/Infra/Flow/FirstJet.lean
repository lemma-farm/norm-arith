-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.SpatialC3
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.FlowOn
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The first spatial jet of a smooth flow is itself a characterized flow on
the product of position and two direction columns. -/
@[expose] public section
open Homogenization
open Filter
open scoped ContDiff Topology
namespace AVenhance.Infra.Flow
noncomputable section
end
end AVenhance.Infra.Flow
