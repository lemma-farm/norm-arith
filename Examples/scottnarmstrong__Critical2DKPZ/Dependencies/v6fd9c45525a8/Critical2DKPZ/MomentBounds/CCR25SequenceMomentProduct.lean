/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.MomentBounds.CCR25SequenceRunCompression
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.MomentBounds.CCR25PartitionMoments
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Moment weights under CCR25 collision-run compression -/
@[expose] public section
open scoped BigOperators
namespace Critical2DKPZ.MomentBounds
noncomputable section
attribute [local instance] Classical.propDecidable
end
end Critical2DKPZ.MomentBounds
