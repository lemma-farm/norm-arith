/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Polymer.PairRecurrence
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Expanding each replica collision factor as `exp(β²) = 1 + σ²` and selecting the earliest nontrivial factor gives the first-collision formula. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Critical2DKPZ.Polymer
end Critical2DKPZ.Polymer
