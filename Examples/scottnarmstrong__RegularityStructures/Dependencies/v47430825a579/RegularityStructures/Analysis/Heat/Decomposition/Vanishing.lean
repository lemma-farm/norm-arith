/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Scaling
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Vanishing of moments by integration by parts

If `J` is a list of coordinate indices in which some index `i` occurs more often than the exponent
`l i` of the monomial `z^l`, then `∫ z^l D_J g = 0` for every smooth compactly supported `g`.
Integrating by parts removes one derivative at a time and differentiates the monomial.
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
private theorem contDiff_parabolicCoords (i : Fin 4) : ContDiff ℝ ∞ fun z => parabolicCoords z i := by
  fin_cases i <;> simp [parabolicCoords] <;> try fun_prop
end RegularityStructures
end
