module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.MainElementaryWeights
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitude
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.AtkinsonCompactProfiles
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.ZetaQuadraticLogGaussianVariation
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaAtkinsonMainWeight (T G L x : ℝ) : ℂ :=
  ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ) *
    (zetaDivisorBandCutoff T G L x : ℂ) * (Real.sqrt x : ℂ) *
      zetaMainMellinProfile (x / T) * zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))
theorem exists_intervalC1Bound_zetaAtkinsonMainWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
      0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (zetaAtkinsonMainWeight T G L) (T / 16) T
        (C * G * Real.sqrt T * Real.log T) := by
  obtain ⟨C, hC, hprofile⟩ := exists_intervalC1Bound_zetaMainMellinProfile
  refine ⟨768 * C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hlog hG hGT hL
  have hT0 : 0 < T := by linarith
  have hinterval : T / 16 ≤ T := by linarith
  have hphase : IntervalC1Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (T / 16) T 1 := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC1Bound_const (zetaSquareReflectedGammaPhase T) (T / 16) T
  have h := (((((intervalC1Bound_source_log hT).mul
    (intervalC1Bound_zetaDivisorBandCutoff hT0 hG hL hinterval) hinterval).mul
      (intervalC1Bound_source_sqrt hT0) hinterval).mul (hprofile T hT0) hinterval).mul
        hphase hinterval).mul (intervalC1Bound_zetaQuadraticLogGaussian hT0 hG hGT) hinterval
  apply h.mono
  have hp : 0 ≤ 256 * C * Real.sqrt Real.pi * G * Real.sqrt T := by positivity
  have hl := mul_le_mul_of_nonneg_left (sourceLogWeight_le_three_log hlog) hp
  convert hl using 1 <;> ring
end MathCollab.Density.Stronger.Atkinson
