/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.HalfTimeBounds
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.FreeMass
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# A heat-potential auxiliary weight

The potential is kept as a positive heat integral. Its heat convolution is
uniformly bounded by a constant times `t^(-1/2)`. In particular it is finite
almost everywhere, without an appeal to a pointwise Riesz-kernel formula.
-/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Critical2DKPZ.DeltaBose
end Critical2DKPZ.DeltaBose
