/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.CumulativeLimit
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.CriticalParameter
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.PrimitiveDerivative
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.ConvexDerivativeLimit
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The marked critical renewal limit

Convexity of the finite coupling polynomial permits differentiating the cumulative
limit. The exact coupling converts that derivative into a marked renewal
function, whose limit is `t j_(ϑ-γ)(t)`.
-/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
