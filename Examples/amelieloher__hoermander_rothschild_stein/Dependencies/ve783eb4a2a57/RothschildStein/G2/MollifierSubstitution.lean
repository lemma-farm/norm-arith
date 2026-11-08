-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.G2.MollifierScale
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)
/-- The scaled convolution has a fixed bump measure after y = Dεz
(BB Prop 3.48 proof, p. 122). The identity respects Bochner defaults. -/
theorem groupRegularize_eq_integral (φ f : (Fin N → ℝ) → ℝ) {ε : ℝ}
    (hε : 0 < ε) (x : Fin N → ℝ) :
    groupRegularize G φ f ε x =
      ∫ z, φ z * f (G.mul (G.inv (G.dilate ε z)) x) := by
  change groupConvolution G _ _ x = _
  rw [groupConvolution_eq_integral]
  simp only [groupMollifierScale, _root_.mul_assoc]
  rw [integral_const_mul]
  have H := integral_dilate G hε
    (fun y => φ (G.dilate ε⁻¹ y) * f (G.mul (G.inv y) x))
  simp only [smul_eq_mul, dilate_inv_dilate G hε.ne'] at H
  exact H.symm
end RothschildStein.G2
