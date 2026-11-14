module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Examples.Example_44723ee067749acf0bd9_TerminalCubicPayment ====
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

def terminalWeightedExcess (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in 0..θ, max (v t - 1) 0 *
    (Real.tan θ * Real.cos t - Real.sin t)


set_option linter.unusedVariables false in
/-- The analytic part of the cubic payment. The envelope is an
almost-everywhere density estimate, and no continuity of `v` is needed. -/
theorem terminalWeightedExcess_le_cubic {v : ℝ → ℝ} {θ t₀ K : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) (ht₀ : 0 ≤ t₀) (hK : 0 ≤ K)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan θ * Real.cos t - Real.sin t)) volume 0 θ)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (v t - 1) 0 ≤ K * max (t - t₀) 0) 
    (h_AmbidextrousSofa_integral_positive_quadratic_tail_kernel : ∀ {θ t₀ : ℝ},
      0 ≤ θ → 0 ≤ t₀ → ∫ (t : ℝ) in 0..θ, Max.max (t - t₀) 0 * (θ - t) = Max.max (θ - t₀) 0 ^ 3 / 6)
    (h_AmbidextrousSofa_terminal_weight_kernel_bounds : ∀ {θ t : ℝ},
      0 ≤ θ →
        θ < Real.pi / 2 →
          t ∈ Set.Icc 0 θ →
            0 ≤ Real.tan θ * Real.cos t - Real.sin t ∧
              Real.tan θ * Real.cos t - Real.sin t ≤ (θ - t) / Real.cos θ)
    :
    terminalWeightedExcess v θ ≤ K * (max (θ - t₀) 0) ^ 3 / (6 * Real.cos θ) := by
  have hmono := intervalIntegral.integral_mono_ae_restrict hθ0 hint
    ((by fun_prop : Continuous fun t : ℝ => K / Real.cos θ * (max (t - t₀) 0 * (θ - t)))
      |>.intervalIntegrable 0 θ) <| by
    filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht htm
    obtain ⟨hk0, hk1⟩ := h_AmbidextrousSofa_terminal_weight_kernel_bounds hθ0 hθL htm
    exact (mul_le_mul ht hk1 hk0 (mul_nonneg hK (le_max_right _ _))).trans_eq (by ring)
  rw [intervalIntegral.integral_const_mul, h_AmbidextrousSofa_integral_positive_quadratic_tail_kernel hθ0 ht₀] at hmono
  exact hmono.trans_eq (by ring)
end AmbidextrousSofa
