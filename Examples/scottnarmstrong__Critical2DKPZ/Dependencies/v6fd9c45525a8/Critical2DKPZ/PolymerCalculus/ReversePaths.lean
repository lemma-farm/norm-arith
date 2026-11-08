/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.PolymerCalculus.TimeReversal
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.WalkKernel
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Reversing a nearest-neighbour path and replacing its steps by their opposites reverses its sequence of visited sites. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Critical2DKPZ.PolymerCalculus
end Critical2DKPZ.PolymerCalculus
