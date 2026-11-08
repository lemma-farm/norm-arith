-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite coefficient matrices as continuous linear maps

A Galerkin weak form starts as a finite matrix of scalar time coefficients. This module assembles
those entries as a bounded operator on the real `PiLp` coefficient space and transfers entrywise
a.e. strong measurability to that operator-valued coefficient.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVenhance.Infra.Parabolic.FourierGalerkin
variable {n : ℕ}
end AVenhance.Infra.Parabolic.FourierGalerkin
end
