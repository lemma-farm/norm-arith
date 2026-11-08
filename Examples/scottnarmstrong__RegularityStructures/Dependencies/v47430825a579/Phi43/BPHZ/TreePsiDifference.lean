/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreePsiMoment
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measurability of the mollified kernel

The mollified Hairer kernel `K_ε = hairerMollifiedKernel N ρ ε`, `K_ε(z) = ∫ K(z - w) ρ_ε^♯(w) dw`,
is measurable (`measurable_hairerMollifiedKernel`). It enters the covariance of the difference
`Ψ_ε - Ψ_ε'` of two scales of the tree `Ψ`.
-/
public section
open MeasureTheory
universe u
namespace RegularityStructures.Phi43
open RegularityStructures
variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}
end RegularityStructures.Phi43
end
