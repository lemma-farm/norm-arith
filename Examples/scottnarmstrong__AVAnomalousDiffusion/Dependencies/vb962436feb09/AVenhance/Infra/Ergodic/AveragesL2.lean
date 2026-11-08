-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Ergodic.AveragesL1
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The corrected L² ergodic estimate -/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus
noncomputable section
end
end AVenhance.Infra.Ergodic
