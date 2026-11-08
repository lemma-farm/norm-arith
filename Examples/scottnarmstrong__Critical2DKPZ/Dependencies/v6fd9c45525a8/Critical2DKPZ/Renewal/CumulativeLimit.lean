/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.WeakLimit
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.HorizonIntegrals
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Cumulative critical renewal convergence

The cumulative renewal mass divided by `log N` converges to the primitive of the
Euler-shifted scalar density. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
