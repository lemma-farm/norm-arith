/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralMetric
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralCompactness
public import Mathlib
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! On a locally compact second-countable Hausdorff space, positive locally finite Borel measures form a Polish space for vague convergence, and compact-window mass bounds characterize relative compactness. -/
public section
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped CompactlySupported Topology
noncomputable section
set_option linter.style.haveILetI false
namespace Critical2DKPZ.RandomMeasure
end Critical2DKPZ.RandomMeasure
end
