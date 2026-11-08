/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Abstract.Datum.HeatFlow
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Abstract.Datum.HeatBounds
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The space-time heat field of a continuous function

For `g ∈ C(T³)`, `heatField g (t, y) = P_t g (y)` for `t > 0` (and `0` otherwise). It is smooth on
`{t > 0}` (`smoothPos_heatField`: for `s > 0` and `t > s` it is the heat flow of the smooth
function `P_s g`, shifted by `s` in time), solves the heat equation (`heatEq_heatField`), and
its spatial derivatives satisfy `|∂_w heatField g (t, y)| ≤ K_m t^{-m/2} ‖g‖`
(`abs_pdWord_heatField_le`).
-/
@[expose] public noncomputable section
namespace RegularityStructures.Datum
open RegularityStructures.PDE
end RegularityStructures.Datum
end
public section
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace RegularityStructures.Datum
open RegularityStructures.PDE
end RegularityStructures.Datum
end
