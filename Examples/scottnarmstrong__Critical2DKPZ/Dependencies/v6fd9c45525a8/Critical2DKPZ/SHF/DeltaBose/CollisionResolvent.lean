/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.BlockL2
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The damped collision resolvent

Above the critical Laplace rate, the repeated-collision kernel integrated against `exp(-rate*t)` has mass and an L² norm bound equal to `4π / (log rate - θ)`. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Critical2DKPZ.DeltaBose
end Critical2DKPZ.DeltaBose
