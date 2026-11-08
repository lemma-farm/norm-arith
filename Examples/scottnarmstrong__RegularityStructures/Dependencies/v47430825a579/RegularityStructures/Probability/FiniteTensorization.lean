/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.Tensorization
public import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# `L²` closure for conditional means

The product variance estimate is most useful when the conditional means are supplied by the
same `L²` hypothesis as the original function.  These lemmas record that closure explicitly.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
namespace RegularityStructures
end RegularityStructures
end
