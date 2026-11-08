-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.Slicing
public import Mathlib
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.Homogenization.Sobolev.CubeEmbedding.FaceReflectionLines
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
/-- The classical coordinate derivative, evaluated in the unit coordinate direction. -/
noncomputable def coordDeriv {d : ℕ} (i : Fin d) (f : Vec d → ℂ) (x : Vec d) : ℂ :=
  fderiv ℝ f x (basisVec i)
end AVenhance.Infra.Torus
