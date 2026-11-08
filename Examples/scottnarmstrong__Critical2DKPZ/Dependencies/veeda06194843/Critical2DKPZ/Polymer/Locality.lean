/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Polymer.Profiles
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Gaussian.TimeBlocks
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Polymer partition functions are measurable with respect to their time interval’s disorder and transform covariantly under simultaneous translations of space and disorder. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Critical2DKPZ.Polymer
end Critical2DKPZ.Polymer
