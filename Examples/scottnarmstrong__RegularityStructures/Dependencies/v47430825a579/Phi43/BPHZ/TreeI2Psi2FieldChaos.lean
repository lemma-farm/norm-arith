/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2FieldFubini
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2FieldMean
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The tree `I(Ψ²) Ψ²`: covariance of kernel-integrated Wick squares, four-argument form

For scales `ε₀, …, ε₃`, noises `ξᵢ`, kernels `g₁, g₃ ∈ L¹`, and points `y, y'`, put
`Yᵢ = :Ψ²_{εᵢ}:` and consider
`E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))]`.
By stochastic Fubini and the diagram formula (W3) for `(Y₀(w), Y₁(y), Y₂(w'), Y₃(y'))` it equals
`∫∫ g₁(w) g₃(w') (χ₄ + χ₂ + χ₀)(w, w') dw dw'` with the chaos-`4`, `2`, `0` kernels
`χ₄, χ₂, χ₀` below, whose entries are the cross covariances
`Q_{εᵢ εⱼ}(zᵢ - zⱼ)` for `(z₀, z₁, z₂, z₃) = (w, y, w', y')` [Hai14, (10.39)-(10.42)].
All three pieces are separately integrable.
-/
@[expose] public noncomputable section
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}
variable {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}
end RegularityStructures.Phi43
end
