/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorPDE
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.Unique
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integration by parts for iterated directional derivatives on `ℝ⁴`

If `ψ` is smooth with compact support and `u` is smooth, then
`∫ (D_d^n u) ψ = (-1)^n ∫ u (D_d^n ψ)`, where `D_d f = f' d`. No decay of `u` is needed.
-/
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
