/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The generator of the auxiliary parabolic semigroup

The auxiliary semigroup `Q_t` on `ℝ⁴` (`RegularityStructures.Analysis.Kernel.ParabolicSemigroup`)
has kernel `q_t(z) = g_t(z₀) ∏ᵢ k_t(zᵢ)` with `g_t = ∫ e^{-tξ²} cos(2πξ·) dξ` and
`k_t = ∫ e^{-tξ⁴} cos(2πξ·) dξ`, so `∂_t g_t = (4π²)⁻¹ ∂² g_t` and `∂_t k_t = -(16π⁴)⁻¹ ∂⁴ k_t`. Its
generator is

  `L φ = (4π²)⁻¹ ∂₀² φ − (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴ φ`,

an operator of parabolic order `ℓ = 4` (Hoshino arXiv:2310.07396v2, Example 2.7, with the
anisotropic `∑ᵢ ∂ᵢ⁴` in place of `Δ²`). Partial derivatives are taken as iterated Fréchet
derivatives along the coordinate directions `timeDir = (1, 0)` and `spaceDir i = (0, eᵢ)`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The time direction `(1, 0)` of `ℝ⁴`. -/
def timeDir : ParabolicSpace := (1, 0)
/-- The space direction `(0, eᵢ)` of `ℝ⁴`. -/
def spaceDir (i : Fin 3) : ParabolicSpace := (0, Pi.single i 1)
end RegularityStructures
end
public section
namespace RegularityStructures
end RegularityStructures
end
