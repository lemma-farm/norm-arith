import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Interval

-- ==== Examples.scottnarmstrong__Superdiffusion.Examples.Example_8cb71d5e91aedca75793_Descent ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
/-!
# Deterministic recurrence integration: adaptive descent

This file formalizes the adaptive descent and its purely ordered telescoping
backbone for ABK26 `l.integrate.approx.recurrence`, Steps 3--4.  The argument
uses a single step-back strong induction, an equivalent presentation of the
paper’s adaptive-chain summation.

## References

* ABK26.
-/
namespace Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
open scoped BigOperators
noncomputable section
namespace Internal
open Real
lemma small_scale_algebra {sm2 nu2 gm cstar cplus γ Kγ β : ℝ}
    (hnu2 : 0 < nu2) (hcstar : 0 < cstar) (hcc : cstar ≤ cplus) (hγ : 0 < γ) (hgm : 0 ≤ gm)
    (hlo : nu2 ≤ sm2) (hup : sm2 ≤ (1 + β) ^ 2 * nu2)
    (hβdef : β = nu2⁻¹ * cplus * γ⁻¹ * gm) (hβ1 : β ≤ 1) (hγ1 : 4 * γ ≤ 1)
    (hKγlo : γ⁻¹ ≤ Kγ) (hKγhi : Kγ ≤ γ⁻¹ + 4) :
    |sm2 - (nu2 + cstar * Kγ * gm)| ≤ 5 * (cplus * γ⁻¹ * gm) := by
  have hγinv : (0:ℝ) ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  set cm := cstar * γ⁻¹ * gm with hcm
  set c := cplus * γ⁻¹ * gm with hc
  have hcmnn : 0 ≤ cm := by rw [hcm]; positivity
  have hcnn : 0 ≤ c := by
    rw [hc]; exact mul_nonneg (mul_nonneg (le_trans hcstar.le hcc) hγinv) hgm
  have hcmc : cm ≤ c := by
    rw [hcm, hc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hγinv) hgm
  have hβc : β * nu2 = c := by
    rw [hβdef, hc,
      show nu2⁻¹ * cplus * γ⁻¹ * gm * nu2 = cplus * γ⁻¹ * gm * (nu2⁻¹ * nu2) by ring,
      inv_mul_cancel₀ (ne_of_gt hnu2), mul_one]
  have hcstargm : cstar * gm = γ * cm := by
    rw [hcm, show γ * (cstar * γ⁻¹ * gm) = cstar * gm * (γ * γ⁻¹) by ring,
      mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
  have hKγc_lo : cm ≤ cstar * Kγ * gm := by
    have h : cstar * γ⁻¹ * gm ≤ cstar * Kγ * gm := by
      linarith only [mul_nonneg (mul_nonneg hcstar.le hgm)
        (by linarith only [hKγlo] : (0:ℝ) ≤ Kγ - γ⁻¹)]
    rwa [← hcm] at h
  have hKγc_hi : cstar * Kγ * gm ≤ 2 * cm := by
    have h1 : cstar * Kγ * gm ≤ cstar * (γ⁻¹ + 4) * gm := by
      linarith only [mul_nonneg (mul_nonneg hcstar.le hgm)
        (by linarith only [hKγhi] : (0:ℝ) ≤ γ⁻¹ + 4 - Kγ)]
    have h2 : cstar * (γ⁻¹ + 4) * gm = cm + 4 * (cstar * gm) := by rw [hcm]; ring
    rw [h2, hcstargm] at h1
    linarith only [h1,
      mul_nonneg (by linarith only [hγ1] : (0:ℝ) ≤ 1 - 4 * γ) hcmnn]
  have hsm_hi : sm2 - nu2 ≤ 3 * c := by
    have h : sm2 - nu2 ≤ 2 * (β * nu2) + β * (β * nu2) := by linarith only [hup]
    rw [hβc] at h
    linarith only [h, mul_nonneg (by linarith only [hβ1] : (0:ℝ) ≤ 1 - β) hcnn]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith only [hlo, hKγc_hi, hcmc, hcnn]
  · linarith only [hsm_hi, hKγc_lo, hcmnn, hcnn]
open Real
open scoped BigOperators
open Real
variable {ν cstar γ E F : ℝ}
end Internal
end
end Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
