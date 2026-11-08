/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Flow.FiniteScaleBlocks
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.GeneralDetermination
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Independence on consecutive time intervals in polymer limits

Compact-test convergence transfers the independence of polymer measures on consecutive time intervals to their limiting random measures. -/
@[expose] public section
open MeasureTheory Filter ProbabilityTheory TopologicalSpace
open scoped CompactlySupported Topology
set_option linter.style.haveILetI false
noncomputable section
namespace Critical2DKPZ.SHF.Flow
open Critical2DKPZ.SHF.Limit
end Critical2DKPZ.SHF.Flow
end
