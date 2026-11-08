/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.SpatialDeriv
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.GaussDeriv
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.HeatTime
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.SmoothDense
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Nonlin
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Semigroup
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# `P_s` maps `C(T³)` into `C¹(T³)` with an `s^{-1/2}` bound

For `h ∈ C(T³)` and `s > 0`, `P_s h` has continuous partial derivatives `V` (`HasTorusDeriv`) with
`‖V‖ ≤ c₁ s^{-1/2} ‖h‖` (`exists_hasTorusDeriv_heatOp`).

For `h` with continuous partial derivatives `Dh`, the Gaussian integration by parts gives
`P_s (∂ᵢ h)(x) = -(2 √s)⁻¹ ∫ zᵢ γ₁(z) h(x - √s z) dz` (`abs_heatOp_deriv_le`). A general `h` is a
uniform limit of smooth functions, and `HasTorusDeriv` is stable under uniform limits
(`hasTorusDeriv_of_tendsto`).
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
