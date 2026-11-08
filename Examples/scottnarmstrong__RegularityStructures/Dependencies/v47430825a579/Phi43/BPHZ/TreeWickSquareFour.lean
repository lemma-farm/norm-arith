/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeWickDifferenceCov
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianWickBlocksFour
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeWickSquare
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Four Wick squares of the tree `Ψ` at several scales

For scales `ε₁, …, ε₄`, noises `ξ₁, …, ξ₄` and points `z₁, …, z₄`, the vector
`(Ψ_{εᵢ}(zᵢ))ᵢ` is a centred Gaussian vector with covariance `c_{ij} = Q_{εᵢ εⱼ}(zᵢ - zⱼ)`, and
the diagram formula (W3) gives
`E[:Ψ²:(z₁) :Ψ²:(z₂) :Ψ²:(z₃) :Ψ²:(z₄)] = χ₄ + χ₂ + χ₀`, where, with `c_{ij}` for `i < j`,

* `χ₄ = 4 c₁₃² c₂₄² + 4 c₁₄² c₂₃² + 16 c₁₃ c₁₄ c₂₃ c₂₄` (no contraction between `(1,3)` and
  `(2,4)` block pairs: chaos `4`),
* `χ₂ = 16 c₁₂ c₃₄ (c₁₃ c₂₄ + c₁₄ c₂₃)` (one contraction in each factor: chaos `2`),
* `χ₀ = 4 c₁₂² c₃₄²` (two contractions in each factor: chaos `0`).

The indices below are `0, 1, 2, 3`.  We also record integrability of the product and the
fourth moment `E[:Ψ²:(z)⁴] = 60 Q_ε(0)⁴`.
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
end RegularityStructures.Phi43
end
