-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Torus.Slicing
public import Mathlib
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.Homogenization.Sobolev.CubeEmbedding.FaceReflectionLines
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Smooth periodic integration by parts on half-open fundamental cells. -/
@[expose] public section
noncomputable section
open MeasureTheory Set intervalIntegral
open Homogenization
namespace AVenhance.Infra.Torus
end AVenhance.Infra.Torus
