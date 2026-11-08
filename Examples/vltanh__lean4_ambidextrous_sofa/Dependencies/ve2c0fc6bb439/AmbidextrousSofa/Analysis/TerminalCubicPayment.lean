module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.TerminalThreeSupports
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.TerminalCircleEndpoints
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.ProperExcessBudget
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.TiltedLateExcessScalar
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# The exact weighted cubic payment for a late companion excess

The weighted error in the proper-terminal comparison is an ordinary
integral of the positive curvature excess. Its trigonometric kernel is
nonnegative before the selected prefix endpoint. A linear late-tail
envelope therefore pays a cubic amount, with all clipping retained.

The overlap is proportional to terminal slope, so its cubic moment
pays the terminal cosine margin throughout the slope range. The same
quadratic half-angle cosine bound supplies the prefix cut.
-/
noncomputable section
open Set Filter MeasureTheory
namespace AmbidextrousSofa
open Analysis
def terminalWeightedExcess (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in 0..θ, max (v t - 1) 0 *
    (Real.tan θ * Real.cos t - Real.sin t)
/-- The positive part makes the formula valid even when the excess has
not begun before the prefix ends. -/
theorem integral_positive_quadratic_tail_kernel {θ t₀ : ℝ}
    (hθ : 0 ≤ θ) (ht₀ : 0 ≤ t₀) :
    (∫ t in 0..θ, max (t - t₀) 0 * (θ - t)) =
      (max (θ - t₀) 0) ^ 3 / 6 := by
  have hc : Continuous (fun t : ℝ => max (t - t₀) 0 * (θ - t)) := by fun_prop
  -- The integrand vanishes before `t₀`.
  have hzero (c : ℝ) (hc0 : 0 ≤ c) (hct : c ≤ t₀) :
      (∫ t in 0..c, max (t - t₀) 0 * (θ - t)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun t ht => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hc0] at ht
    simp [max_eq_right (show t - t₀ ≤ 0 by linarith [ht.2])]
  rcases le_total θ t₀ with hθt | htθ
  · rw [hzero θ hθ hθt, max_eq_right (sub_nonpos.mpr hθt)]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 t₀)
    (hc.intervalIntegrable t₀ θ), hzero t₀ ht₀ le_rfl, zero_add, max_eq_left (sub_nonneg.mpr htθ),
    ← Analysis.integral_quadratic_tail_kernel]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le htθ] at ht
  simp [max_eq_left (sub_nonneg.mpr ht.1)]
theorem terminal_weight_kernel_eq {θ t : ℝ} (hcos : Real.cos θ ≠ 0) :
    Real.tan θ * Real.cos t - Real.sin t =
      Real.sin (θ - t) / Real.cos θ := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub]
  field_simp
theorem terminal_weight_kernel_bounds {θ t : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) (ht : t ∈ Icc 0 θ) :
    0 ≤ Real.tan θ * Real.cos t - Real.sin t ∧
      Real.tan θ * Real.cos t - Real.sin t ≤ (θ - t) / Real.cos θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθL⟩
  rw [terminal_weight_kernel_eq hc.ne']
  refine ⟨div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [ht.2]) (by linarith [ht.1, Real.pi_pos])) hc.le, ?_⟩
  exact div_le_div_of_nonneg_right (Real.sin_le (by linarith [ht.2])) hc.le
/-- The analytic part of the cubic payment. The envelope is an
almost-everywhere density estimate, and no continuity of `v` is needed. -/
theorem terminalWeightedExcess_le_cubic {v : ℝ → ℝ} {θ t₀ K : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) (ht₀ : 0 ≤ t₀) (hK : 0 ≤ K)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan θ * Real.cos t - Real.sin t)) volume 0 θ)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (v t - 1) 0 ≤ K * max (t - t₀) 0) :
    terminalWeightedExcess v θ ≤ K * (max (θ - t₀) 0) ^ 3 / (6 * Real.cos θ) := by
  have hmono := intervalIntegral.integral_mono_ae_restrict hθ0 hint
    ((by fun_prop : Continuous fun t : ℝ => K / Real.cos θ * (max (t - t₀) 0 * (θ - t)))
      |>.intervalIntegrable 0 θ) <| by
    filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht htm
    obtain ⟨hk0, hk1⟩ := terminal_weight_kernel_bounds hθ0 hθL htm
    exact (mul_le_mul ht hk1 hk0 (mul_nonneg hK (le_max_right _ _))).trans_eq (by ring)
  rw [intervalIntegral.integral_const_mul, integral_positive_quadratic_tail_kernel hθ0 ht₀] at hmono
  exact hmono.trans_eq (by ring)
end AmbidextrousSofa
