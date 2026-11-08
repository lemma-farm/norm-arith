/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.PointToPoint
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.PointToPlane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.ProfileP2Fun
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.SmoothedP2Plane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.SrwKernel
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite polymer path weights include disorder at times `a+1,…,a+n`, as in equation (1.3), and yield measurable partition functions supported on reachable endpoints. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Critical2DKPZ.Polymer
end Critical2DKPZ.Polymer
