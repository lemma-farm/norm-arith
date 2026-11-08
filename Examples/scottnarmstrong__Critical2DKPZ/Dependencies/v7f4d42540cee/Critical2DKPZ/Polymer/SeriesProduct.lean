/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Polymer.Series
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Polymer.Orthogonality
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Two series whose L² norms are summable admit termwise integration of their product. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Critical2DKPZ.Polymer
end Critical2DKPZ.Polymer
