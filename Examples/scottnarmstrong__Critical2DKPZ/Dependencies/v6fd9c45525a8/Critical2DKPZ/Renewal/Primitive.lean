/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.HorizonCutoff
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The cumulative scalar renewal density

The singular scalar density is integrable at time zero. Its positive, continuous
primitive is the coefficient of `log N` in the free second moment.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
