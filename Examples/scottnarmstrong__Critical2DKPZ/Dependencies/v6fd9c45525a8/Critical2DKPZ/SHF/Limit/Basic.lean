/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Definitions.IsCriticalSHF
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Moments.PairingFubini
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Polymer random measures and their subsequential limits

The limit condition requires joint convergence of compact and flat pairings at finitely many time pairs. -/
@[expose] public section
open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology
noncomputable section
namespace Critical2DKPZ.SHF.Limit
end Critical2DKPZ.SHF.Limit
end
