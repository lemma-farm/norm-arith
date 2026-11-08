-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.LinearWindowBounds
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! A local quadratic remainder estimate for a flow and its variational
equation. All bounds are confined to one compact forward time window and one
bounded state tube. -/
@[expose] public section
open Set
open scoped NNReal Topology
namespace AVenhance.Infra.Flow
noncomputable section
end
end AVenhance.Infra.Flow
