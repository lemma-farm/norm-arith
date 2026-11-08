/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralBorel
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! On a locally compact second-countable Hausdorff space, a measurable random measure that is locally finite almost surely has a measurable, everywhere locally finite modification with the same almost-sure values. -/
public section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
noncomputable section
set_option linter.style.haveILetI false
namespace Critical2DKPZ.RandomMeasure
end Critical2DKPZ.RandomMeasure
end
