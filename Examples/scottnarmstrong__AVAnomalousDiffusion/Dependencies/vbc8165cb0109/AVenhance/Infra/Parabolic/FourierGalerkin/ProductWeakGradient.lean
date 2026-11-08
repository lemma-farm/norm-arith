-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.ProductPathIdentification
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.TorusBridge
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Statements.Roots.L2NormSq
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Spatial derivative tests for the synchronized Galerkin limit

The Galerkin gradients are weak derivatives on the torus. This module begins the corresponding
closedness argument in the synchronized product-space limit.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance productWeakGradientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance productWeakGradientOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
end AVenhance.Infra.Parabolic.FourierGalerkin
end
