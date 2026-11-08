-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.G2.InversePolynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory Function
variable {N : ℕ} (G : HomogeneousGroup N)
/-- Left translation is triangular unipotent (BB Theorem 3.6(b), p. 96). -/
theorem leftTranslation_isTriangular (y : Fin N → ℝ) :
    IsTriangular (G.mul y) (fun _ => 1) := by
  intro k x x' hxx'
  rw [mul_coordinate, mul_coordinate, correction_eval_congr G k (fun _ _ => rfl) hxx']
  ring
theorem measurePreserving_leftTranslation (y : Fin N → ℝ) : MeasurePreserving (G.mul y) :=
  (triangular_measurePreserving_bijective _ _
    ((continuous_mul G).comp (continuous_const.prodMk continuous_id)).measurable
    (fun _ => Or.inl rfl) (leftTranslation_isTriangular G y)).1
theorem measurePreserving_inv : MeasurePreserving G.inv :=
  (triangular_measurePreserving_bijective _ _ (continuous_inv G).measurable
    (fun _ => Or.inr rfl) (inv_isTriangular G)).1
/-- Left translation is bijective (BB Theorem 3.6(d), p. 96). -/
theorem leftTranslation_bijective (y : Fin N → ℝ) : Bijective (G.mul y) :=
  (triangular_measurePreserving_bijective _ _
    (measurePreserving_leftTranslation G y).measurable
    (fun _ => Or.inl rfl) (leftTranslation_isTriangular G y)).2
theorem inv_bijective : Bijective G.inv :=
  ⟨(Function.LeftInverse.injective (inv_inv G)), Function.RightInverse.surjective (inv_inv G)⟩
end RothschildStein.G2
