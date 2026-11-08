-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.G2.ConvolutionDefs
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
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)
theorem measurePreserving_leftInvAt (x : Fin N → ℝ) :
    MeasurePreserving (fun w : Fin N → ℝ => G.mul x (G.inv w)) :=
  (measurePreserving_leftTranslation G x).comp (measurePreserving_inv G)
/-- The first and second BB Bochner formulas agree. The equality
also respects the Bochner default outside the absolute-convergence domain;
no convergence is inferred there (BB (3.27), p. 119). -/
theorem groupConvolution_eq_integral {𝕜 : Type*} [RCLike 𝕜]
    (f g : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ) :
    groupConvolution G f g x = ∫ y, f y * g (G.mul (G.inv y) x) := by
  rw [groupConvolution_def]
  let F : (Fin N → ℝ) → 𝕜 := fun y => f y * g (G.mul (G.inv y) x)
  have hp := measurePreserving_leftInvAt G x
  have he : MeasurableEmbedding (fun w : Fin N → ℝ => G.mul x (G.inv w)) :=
    hp.measurable.measurableEmbedding
      ((leftTranslation_bijective G x).comp (inv_bijective G)).injective
  have h := hp.integral_comp he F
  simpa only [F, inv_product, inv_inv, mul_assoc, inv_mul, mul_zero] using h
end RothschildStein.G2
