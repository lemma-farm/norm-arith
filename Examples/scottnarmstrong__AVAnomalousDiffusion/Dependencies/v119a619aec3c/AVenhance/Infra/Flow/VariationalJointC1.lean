-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.JointC1Core
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.JointSpatialDerivative
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.JointSpatialDerivativeAll
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.JointC1
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.SecondJetContinuity
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.FirstJet
public import Mathlib
public import Mathlib.Analysis.Matrix.Normed
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Joint C¹ regularity of the variational flow on forward regions. -/
@[expose] public section
open Homogenization
open Set
open scoped ContDiff Topology
namespace AVenhance.Infra.Flow
noncomputable section
local instance avInfraFlowVariationalJointC1NormedAddCommGroup1 : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.normedAddCommGroup
local instance avInfraFlowVariationalJointC1NormedSpace2 : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.normedSpace
end
end AVenhance.Infra.Flow
