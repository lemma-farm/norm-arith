/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.MarkedUniformLimit
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.PositiveArray
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomWalk.ReplicaOverlap
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The local critical renewal limit

The differentiated renewal identity expresses a local renewal mass as a return-kernel
first moment tested against the marked renewal mass. The marked cumulative limit and the
period-two local central limit theorem then give the local density, uniformly on compact
positive-time and critical-parameter windows.
-/
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
