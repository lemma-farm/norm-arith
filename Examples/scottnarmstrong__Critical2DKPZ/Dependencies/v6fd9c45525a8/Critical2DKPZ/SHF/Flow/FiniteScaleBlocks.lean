/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Limit.Tightness
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.Locality
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.PolymerCalculus.Clocks
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Definitions.RescaledP2P
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Finite-scale independence of polymer measures on consecutive slabs

Each finite-scale polymer measure is measurable with respect to the disorder
coordinates in its time slab. Successive slabs therefore give independent
measure-valued random variables.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal CompactlySupported Topology
set_option linter.style.haveILetI false
noncomputable section
namespace Critical2DKPZ.SHF.Flow
open Critical2DKPZ.SHF.Limit
end Critical2DKPZ.SHF.Flow
end
