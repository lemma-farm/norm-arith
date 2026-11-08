/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.GaussDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Comp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The time derivative of the heat operator

For `g ∈ C(T³, E)` with continuous first and second derivatives `Dg`, `D²g` on the lift, and
`t > 0`, `∂_t P_t g(x) = P_t(Δg)(x)`, where `Δg = Σᵢ D²g(eᵢ, eᵢ)`.

With `P_t g(x) = ∫ γ₁(z) g(x - √t z) dz`, differentiation in `t` gives
`-(2√t)⁻¹ ∫ γ₁(z) Dg(x - √t z) z dz`, and the Gaussian integration by parts
`∫ zᵢ γ₁(z) φ(z) dz = 2 ∫ γ₁(z) ∂ᵢ φ(z) dz` turns this into `∫ γ₁(z) Δg(x - √t z) dz`.
-/
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end RegularityStructures.PDE
end
public section
open MeasureTheory Real Filter Topology Set
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end RegularityStructures.PDE
end
