-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.SpaceGrad
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Real-valued periodic integration by parts for Galerkin tests

This bridge specializes the landed complex torus-calculus theorem to the real gradient and
the open unit-cell carrier used by the parabolic weak formulation.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
namespace AVenhance.Infra.Parabolic.FourierGalerkin
end AVenhance.Infra.Parabolic.FourierGalerkin
end
