-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.JointSmoothBootstrap
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.FiniteSpatialJetSmooth
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.Laws
public import Mathlib
public import Mathlib.Topology.Algebra.Module.FiniteDimension
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Joint smoothness from fixed-start smoothness and the global flow law. -/
@[expose] public section
open Homogenization
open Filter
open scoped ContDiff Topology
namespace AVenhance.Infra.Flow
noncomputable section
end
end AVenhance.Infra.Flow
