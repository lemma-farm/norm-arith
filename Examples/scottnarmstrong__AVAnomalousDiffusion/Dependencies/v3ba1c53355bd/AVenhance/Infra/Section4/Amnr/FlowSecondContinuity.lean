-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Flow.SecondVariationContinuity
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Flow.SpatialC2
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Flow.JointSpatialDerivativeAll
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Joint continuity of the actual second flow derivative, with a fixed start.
This is the regularity needed to admit the primitive material flow jet. -/
@[expose] public section
noncomputable section
open Homogenization Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow
end AVenhance.Infra.Section4
