/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.KernelBlocks
public import Mathlib
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The nonnegative collision-diagram series

Each collision word contributes the ordered time-space integral in Tsai (2024), equation (2.13), with product Lebesgue measure on the free collision coordinates. The moment kernel is the free kernel plus the sum over nonempty words; at one particle the collision correction vanishes, and at two particles only the single resummed collision term remains. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Critical2DKPZ.DeltaBose
end Critical2DKPZ.DeltaBose
