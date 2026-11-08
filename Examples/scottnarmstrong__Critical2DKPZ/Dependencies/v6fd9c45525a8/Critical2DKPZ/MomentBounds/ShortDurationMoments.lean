/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.SmoothedCovariance
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.MomentBounds.CCR25GaussianMoments
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Finite-horizon Gaussian path moments -/
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
namespace Critical2DKPZ.MomentBounds
noncomputable section
end
end Critical2DKPZ.MomentBounds
