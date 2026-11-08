/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.MarkedLimit
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.LocalBounds
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.MonotoneUniform
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Locally uniform marked renewal convergence

The marked profile is increasing in the critical parameter and in time. Joint
continuity of the scalar density upgrades its pointwise limit to uniform convergence
on every compact set of critical parameters and strictly positive times.
-/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Uniformity
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
