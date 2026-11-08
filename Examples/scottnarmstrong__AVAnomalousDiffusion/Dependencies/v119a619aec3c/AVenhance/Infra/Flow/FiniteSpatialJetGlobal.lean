-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.FiniteSpatialJet
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.LinearGlobalExistence
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Global recursive jet flows, built by solving each new derivative level as
a linear equation along the preceding jet trajectory. -/
@[expose] public section
open Homogenization
open scoped ContDiff Topology
namespace AVenhance.Infra.Flow
noncomputable section
end
end AVenhance.Infra.Flow
