-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section3.SpaceAverages
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Section3.ChiM
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Section3.PsiM
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Section3.Flux
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The cutoff separation that reduces the spatial flux to one active shear. -/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
namespace AVenhance.Infra.Section3
open AVenhance
end AVenhance.Infra.Section3
