/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Abstract.Datum.HeatDeriv1
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# `P_s g` is smooth with derivative bounds, for continuous `g`

For `g ∈ C(T³)` and `s > 0`, the lift `φ = P_s g ∘ torusProj` is `C^∞` on `ℝ³`
(`contDiff_lift_heatOp`), and every spatial derivative of order `m` is again of the form
`P_{s/2^m} g''` with `‖g''‖ ≤ K_m s^{-m/2} ‖g‖` (`exists_sdWord_heatOp`). The mechanism is
`∂ᵢ P_s g = P_{s/2} (∂ᵢ P_{s/2} g)` (`exists_sdLift_heatOp`), where `∂ᵢ P_{s/2} g` is a continuous
function bounded by `c₁ (s/2)^{-1/2} ‖g‖`.
-/
open scoped ContDiff
@[expose] public noncomputable section
namespace RegularityStructures.Datum
open RegularityStructures.PDE
end RegularityStructures.Datum
end
public section
open MeasureTheory Filter Topology Real
open scoped ContDiff
namespace RegularityStructures.Datum
open RegularityStructures.PDE
end RegularityStructures.Datum
end
