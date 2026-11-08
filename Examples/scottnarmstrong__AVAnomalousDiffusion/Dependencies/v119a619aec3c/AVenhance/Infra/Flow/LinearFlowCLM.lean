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
/-! Continuous linear dependence on initial data for finite-window linear ODEs. -/
@[expose] public section
open Set
open scoped NNReal Topology
namespace AVenhance.Infra.Flow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end
end AVenhance.Infra.Flow
