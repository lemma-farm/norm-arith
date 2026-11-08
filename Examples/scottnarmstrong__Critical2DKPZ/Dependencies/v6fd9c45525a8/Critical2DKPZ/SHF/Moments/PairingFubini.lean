/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Moments.AnnealedPairing
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.Profiles
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.SummableCovariance
import Mathlib
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Integrable random pairings and first-moment limits

Joint measurability and absolute integrability allow disorder expectations to commute with compactly supported spatial pairings, giving convergence of first pairing moments. -/
public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.SHF.Moments
open Polymer
end Critical2DKPZ.SHF.Moments
