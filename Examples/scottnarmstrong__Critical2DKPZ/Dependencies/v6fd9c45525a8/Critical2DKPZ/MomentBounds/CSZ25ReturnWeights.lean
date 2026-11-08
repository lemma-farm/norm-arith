/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.LocalLimit
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.WalkKernel
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Two-sided reciprocal bounds for collision return weights

These are the constants `aMinus, aPlus` used in CSZ25 Section 5. Positivity at every even time
and the period-correct local limit give uniform bounds without an asymptotic cutoff.
-/
@[expose] public noncomputable section
open Critical2DKPZ.Renewal
namespace Critical2DKPZ.MomentBounds
end Critical2DKPZ.MomentBounds
