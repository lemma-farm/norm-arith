/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Tsai.Defs
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Compact tensor tests and dense endpoint approximations

Products of compactly supported continuous endpoint functions give compact
continuous tests on the plane pair. Every spatial `L²` representative is the
`L²` limit of such endpoint tests.
-/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology CompactlySupported
namespace Critical2DKPZ.SHF.Tsai
end Critical2DKPZ.SHF.Tsai
end
