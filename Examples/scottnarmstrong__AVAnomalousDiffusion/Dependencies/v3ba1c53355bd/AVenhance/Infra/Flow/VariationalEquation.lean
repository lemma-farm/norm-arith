-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Flow.IsFlow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Flow.FlowIntegral
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Flow.SmoothField
public import Mathlib
public import Mathlib.Analysis.Normed.Operator.Bilinear
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The linear variational equation along a characterized flow trajectory. -/
@[expose] public section
open Homogenization
open scoped ContDiff NNReal Topology
namespace AVenhance.Infra.Flow
end AVenhance.Infra.Flow
