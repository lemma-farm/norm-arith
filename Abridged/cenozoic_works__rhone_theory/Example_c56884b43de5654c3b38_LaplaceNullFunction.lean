module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_c56884b43de5654c3b38_LaplaceNullFunction ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # A nonzero bounded continuous function with vanishing Laplace transforms at `k(k-1)/2` -/
@[expose] public section
namespace Rhone.Analysis
open MeasureTheory Set Filter Complex
open scoped Topology FourierTransform


set_option linter.unusedVariables false in
theorem integrable_div_sq_add_sq {β : ℂ} (hβ2 : 0 < (β ^ 2).re) (C : ℂ) {g : ℝ → ℂ}
    (hg : Continuous g) (hgn : ∀ y, ‖g y‖ ≤ 1) 
    (h_Rhone_Analysis_sq_add_sq_ne_zero : ∀ {β : ℂ}, 0 < (β ^ 2).re → ∀ (y : ℝ), β ^ 2 + (↑y : ℂ) ^ 2 ≠ 0)
    (h_Rhone_Analysis_norm_sq_add_sq_ge : ∀ (β : ℂ) (y : ℝ), Min.min (β ^ 2).re 1 * (1 + y ^ 2) ≤ ‖β ^ 2 + (↑y : ℂ) ^ 2‖)
    :
    Integrable (fun y : ℝ => g y * (C / (β ^ 2 + (y : ℂ) ^ 2))) := by
  set m := min (β ^ 2).re 1
  have hm : 0 < m := lt_min hβ2 one_pos
  refine (integrable_inv_one_add_sq.const_mul (‖C‖ / m)).mono' ?_ ?_
  · refine (hg.mul ?_).aestronglyMeasurable
    exact continuous_const.div (by fun_prop) (h_Rhone_Analysis_sq_add_sq_ne_zero hβ2)
  · filter_upwards with y
    have hpos : 0 < m * (1 + y ^ 2) := by positivity
    rw [norm_mul, norm_div]
    calc ‖g y‖ * (‖C‖ / ‖β ^ 2 + (y : ℂ) ^ 2‖) ≤ 1 * (‖C‖ / (m * (1 + y ^ 2))) := by
          gcongr
          · exact hgn y
          · exact h_Rhone_Analysis_norm_sq_add_sq_ge β y
      _ = ‖C‖ / m * (1 + y ^ 2)⁻¹ := by field_simp
end Rhone.Analysis
