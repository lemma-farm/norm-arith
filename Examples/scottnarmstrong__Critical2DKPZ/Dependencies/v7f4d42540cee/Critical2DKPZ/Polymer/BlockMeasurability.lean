/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Polymer.Locality
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Polymer.SmoothedCovariance
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Definitions.EndpointDist
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Definitions.SmoothedEndpointDist
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Block locality of averaged partition functions and endpoint distributions -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Critical2DKPZ.Polymer
end Critical2DKPZ.Polymer
