/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralPolish
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralRandom
public import Mathlib
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! A sequence of Borel probability laws on a countable product of copies of a Hausdorff space is tight if its coordinate marginals are tight. In a Polish space, every tight sequence of probability laws has a weakly convergent subsequence. -/
public section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
noncomputable section
set_option linter.style.haveILetI false
namespace Critical2DKPZ.RandomMeasure
end Critical2DKPZ.RandomMeasure
end
