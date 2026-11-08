/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.Moments.Replica
import Mathlib
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Changing endpoints in time sums

Switching between the time sets `1, …, n` and `0, …, n - 1` changes only the endpoint terms. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Critical2DKPZ.SHF.Moments
end Critical2DKPZ.SHF.Moments
