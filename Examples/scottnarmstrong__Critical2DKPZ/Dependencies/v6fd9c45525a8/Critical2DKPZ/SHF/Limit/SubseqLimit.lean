/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Limit.JointTightness
import Mathlib
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # First marginals of subsequential polymer limits

Gaussian tail bounds identify the first-marginal coordinate of a joint vague polymer limit with the projection of its pair-measure coordinate. -/
@[expose] public section
open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology BoundedContinuousFunction ENNReal
noncomputable section
set_option linter.style.haveILetI false
namespace Critical2DKPZ.SHF.Limit
end Critical2DKPZ.SHF.Limit
end
