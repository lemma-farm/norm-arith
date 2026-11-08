-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.WeakLimitEquation
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite Galerkin weak form in product-space pairings

The finite ODE identity is expressed using the product-space Hilbert classes so that it can be
passed directly through weak convergence.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
end AVenhance.Infra.Parabolic.FourierGalerkin
end
