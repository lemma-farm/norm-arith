module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.ScaledGaussianKernel
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Normalized Gaussian averages remain continuous in the terminal Banach
norm at zero variance. Uniform continuity is required only of the bounded
observable; it is part of the terminal space's highest-jet condition. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory
theorem scaledGaussianNormalizer_apply (p : ColeHopfParameter) (x : ℝ) :
    scaledGaussianNormalizer p x = ∫z,
      Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x))
        ∂gaussianReal 0 1 := by
  change (BoundedContinuousFunction.evalCLM ℝ x)
    (∫z,scaledGaussianKernel p z ∂gaussianReal 0 1) = _
  rw [←ContinuousLinearMap.integral_comp_comm _ (integrable_scaledGaussianKernel p)]
  simp only [BoundedContinuousFunction.evalCLM_apply,scaledGaussianKernel_apply]
def scaledGaussianLower (c : ℝ) : ℝ :=
  ∫z,Real.exp (-c*‖z‖) ∂gaussianReal 0 1
theorem integrable_scaledGaussianLower (c : ℝ) :
    Integrable (fun z => Real.exp (-c*‖z‖)) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs_gaussianReal 0 1 (-c)
theorem scaledGaussianLower_le (p : ColeHopfParameter) (c : ℝ)
    (hc : ‖p.1.1‖*‖p.1.2‖*‖p.2‖ ≤ c) (x : ℝ) :
    scaledGaussianLower c ≤ scaledGaussianNormalizer p x := by
  rw [scaledGaussianNormalizer_apply]
  have hi : Integrable (fun z =>
      Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)))
      (gaussianReal 0 1) := by
    simpa only [BoundedContinuousFunction.evalCLM_apply,scaledGaussianKernel_apply] using
      ((BoundedContinuousFunction.evalCLM ℝ x).integrable_comp (integrable_scaledGaussianKernel p))
  change (∫z,Real.exp (-c*‖z‖) ∂gaussianReal 0 1) ≤ _
  apply integral_mono (integrable_scaledGaussianLower c) hi
  intro z
  apply Real.exp_le_exp.mpr
  have hi := norm_terminalValue_sub_le p.2 x (x+p.1.2*z)
  simp only [add_sub_cancel_left] at hi
  have hnorm : ‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ ≤ c*‖z‖ := by
    rw [norm_mul]
    calc
      ‖p.1.1‖*‖terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x‖
        ≤ ‖p.1.1‖*(‖p.2‖*‖p.1.2*z‖) := by
          gcongr
          exact hi.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0) (norm_nonneg _))
      _ = (‖p.1.1‖*‖p.1.2‖*‖p.2‖)*‖z‖ := by rw [norm_mul]; ring
      _ ≤ c*‖z‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  calc
    -c*‖z‖ ≤ -‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ := by
      simpa only [neg_mul] using neg_le_neg hnorm
    _ ≤ p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x) := neg_abs_le _
end GeneralDepthPaper
