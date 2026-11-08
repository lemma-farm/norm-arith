module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scalar reverse-time energy representatives

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
private theorem tendsto_integral_mul_of_tendsto_integral_abs
    {μ : Measure ℝ} {F : ℝ → ℝ → ℝ} {f phi : ℝ → ℝ}
    (hF : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (F h) μ)
    (hf : Integrable f μ) (hphi : AEStronglyMeasurable phi μ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ‖phi t‖ ≤ C)
    (hlim : Tendsto (fun h : ℝ => ∫ t, |F h t - f t| ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t, F h t * phi t ∂μ) (𝓝[>] 0)
      (𝓝 (∫ t, f t * phi t ∂μ)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnorm : ∀ t : ℝ, ‖‖phi t‖‖ ≤ C := by
    intro t
    simpa only [norm_norm] using hC t
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact (norm_nonneg _).trans this
  have herr : Tendsto (fun h : ℝ => ∫ t, (F h t - f t) * phi t ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · filter_upwards with h
      exact norm_nonneg _
    · filter_upwards [hF] with h hF
      have hdiff : Integrable (fun t => F h t - f t) μ := hF.sub hf
      have hprod : Integrable (fun t => |F h t - f t| * ‖phi t‖) μ :=
        hdiff.norm.mul_bdd hphi.norm (Eventually.of_forall fun t => hCnorm t)
      calc
        ‖∫ t, (F h t - f t) * phi t ∂μ‖ ≤
            ∫ t, ‖(F h t - f t) * phi t‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ t, |F h t - f t| * ‖phi t‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with t
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ ∫ t, C * |F h t - f t| ∂μ := by
          apply integral_mono
          · exact hprod
          · exact hdiff.norm.const_mul C
          · intro t
            calc
              |F h t - f t| * ‖phi t‖ ≤ |F h t - f t| * C :=
                mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)
              _ = C * |F h t - f t| := mul_comm _ _
        _ = C * (∫ t, |F h t - f t| ∂μ) :=
          integral_const_mul C (fun t => |F h t - f t|)
    · simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have hsum : Tendsto (fun h : ℝ =>
      (∫ t, (F h t - f t) * phi t ∂μ) + ∫ t, f t * phi t ∂μ)
      (𝓝[>] 0) (𝓝 (∫ t, f t * phi t ∂μ)) := by
    simpa only [zero_add] using herr.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [hF] with h hF
  have hdiff : Integrable (fun t => F h t - f t) μ := hF.sub hf
  have hprod : Integrable (fun t => (F h t - f t) * phi t) μ :=
    hdiff.mul_bdd hphi (Eventually.of_forall fun t => hC t)
  have hraw : Integrable (fun t => f t * phi t) μ :=
    hf.mul_bdd hphi (Eventually.of_forall fun t => hC t)
  rw [← integral_add hprod hraw]
  apply integral_congr_ae
  filter_upwards with t
  ring
end HypoellipticAleksandrov.Parabolic.Dirichlet
