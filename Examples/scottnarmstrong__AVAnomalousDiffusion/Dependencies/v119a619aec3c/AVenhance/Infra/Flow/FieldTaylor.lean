-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.PeriodicSmooth
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.VariationalEquation
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Second-order Taylor control for smooth periodic vector fields. -/
@[expose] public section
open Homogenization
open scoped ContDiff NNReal Topology
namespace AVenhance.Infra.Flow
end AVenhance.Infra.Flow
