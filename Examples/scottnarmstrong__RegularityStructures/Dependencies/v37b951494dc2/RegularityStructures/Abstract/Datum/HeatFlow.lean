/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Abstract.Datum.HeatSmooth
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.MildSmooth
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The free heat flow of smooth data

For smooth `w ∈ C(T³)`, `t ↦ P_t w` is the mild solution of `∂_t u = Δu` with `G = 0`, so the
results of `RegularityStructures.PDE.MildSmooth` and `RegularityStructures.PDE.MildTime` apply:
`(t, y) ↦ P_t w (y)` is `C^∞` on `(0, ∞) × ℝ³` (`contDiffOn_heatFlow`) and `∂_t P_t w = Δ P_t w`
(`heatFlow_deriv`).
-/
open scoped ContDiff
public section
open MeasureTheory Set Filter Topology
namespace RegularityStructures.Datum
open RegularityStructures.PDE
end RegularityStructures.Datum
end
