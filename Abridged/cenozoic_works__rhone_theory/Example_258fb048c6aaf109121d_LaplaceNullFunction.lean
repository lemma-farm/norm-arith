module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_258fb048c6aaf109121d_LaplaceNullFunction ====
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
noncomputable def nullBeta : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * (2 + ((Real.pi / 2 : ℝ) : ℂ) * I)

noncomputable def laplaceNullFunction (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
    (nullBeta * cexp (-nullBeta ^ 2 / t)).re * (Real.exp (-t / 8) / (t * Real.sqrt t))


set_option linter.unusedVariables false in
theorem abs_laplaceNullFunction_le_mul (t : ℝ) 
    (h_Rhone_Analysis_abs_laplaceNullFunction_le : ∀ {t : ℝ},
      0 < t →
        |Rhone.Analysis.laplaceNullFunction t| ≤
          ‖Rhone.Analysis.nullBeta‖ * (Real.exp (-(Rhone.Analysis.nullBeta ^ 2).re / t) / (t * √t)))
    (h_Rhone_Analysis_nullBeta_sq_re_pos : 0 < (Rhone.Analysis.nullBeta ^ 2).re)
    (h_Rhone_Analysis_exp_neg_div_le : ∀ {r t : ℝ}, 0 < r → 0 < t → Real.exp (-r / t) ≤ 6 * t ^ 3 / r ^ 3)
    :
    |laplaceNullFunction t| ≤
      6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (|t| * Real.sqrt |t|) := by
  have hr := h_Rhone_Analysis_nullBeta_sq_re_pos
  rcases le_or_gt t 0 with ht | ht
  · simp only [laplaceNullFunction, ht, ite_true, abs_zero]; positivity
  · refine (h_Rhone_Analysis_abs_laplaceNullFunction_le ht).trans ?_
    rw [abs_of_pos ht]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have he := h_Rhone_Analysis_exp_neg_div_le hr ht
    calc ‖nullBeta‖ * (Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t))
        ≤ ‖nullBeta‖ * (6 * t ^ 3 / (nullBeta ^ 2).re ^ 3 / (t * Real.sqrt t)) := by gcongr
      _ = 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (t * Real.sqrt t) := by
        field_simp
        have h2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
        have h3 := mul_le_mul_of_nonneg_left (le_of_eq h2) (norm_nonneg nullBeta)
        have h4 := mul_le_mul_of_nonneg_left (le_of_eq h2.symm) (norm_nonneg nullBeta)
        nlinarith [h3, h4, norm_nonneg nullBeta]
end Rhone.Analysis
