/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Moment
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The heat kernel decomposition satisfies Assumption 5.1 with `β = 2`

`isRegularisingDecomposition_heatShell : IsRegularisingDecomposition (fun n x y => heatShell n (x - y)) 2`.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5 and Assumption 5.1 ((5.3)–(5.5)).
-/
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
