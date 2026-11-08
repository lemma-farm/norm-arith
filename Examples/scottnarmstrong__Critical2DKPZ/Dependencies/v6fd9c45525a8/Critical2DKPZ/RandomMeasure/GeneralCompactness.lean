/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralBorel
public import Mathlib
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! On a locally compact second-countable Hausdorff space, uniform bounds on mass over a compact exhaustion give a vaguely convergent subsequence. -/
@[expose] public section
open MeasureTheory Set Topology Filter
open scoped CompactlySupported
noncomputable section
set_option linter.style.haveILetI false
namespace Critical2DKPZ.RandomMeasure
end Critical2DKPZ.RandomMeasure
end
