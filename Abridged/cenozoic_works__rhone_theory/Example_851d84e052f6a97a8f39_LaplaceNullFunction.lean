module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_851d84e052f6a97a8f39_LaplaceNullFunction ====
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
theorem bounded_laplaceNullFunction 
    (h_Rhone_Analysis_nullBeta_sq_re_pos : 0 < (Rhone.Analysis.nullBeta ^ 2).re)
    (h_Rhone_Analysis_abs_laplaceNullFunction_le : ∀ {t : ℝ},
      0 < t →
        |Rhone.Analysis.laplaceNullFunction t| ≤
          ‖Rhone.Analysis.nullBeta‖ * (Real.exp (-(Rhone.Analysis.nullBeta ^ 2).re / t) / (t * √t)))
    (h_Rhone_Analysis_abs_laplaceNullFunction_le_mul : ∀ (t : ℝ),
      |Rhone.Analysis.laplaceNullFunction t| ≤
        6 * ‖Rhone.Analysis.nullBeta‖ / (Rhone.Analysis.nullBeta ^ 2).re ^ 3 * (|t| * √|t|))
    : ∃ B : ℝ, ∀ t, |laplaceNullFunction t| ≤ B := by
  set K := 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3
  have hK : 0 ≤ K := by have := h_Rhone_Analysis_nullBeta_sq_re_pos; positivity
  have hβn : 0 ≤ ‖nullBeta‖ := norm_nonneg _
  refine ⟨‖nullBeta‖ + K, fun t => ?_⟩
  rcases le_or_gt t 0 with h0 | h0
  · simp only [laplaceNullFunction, h0, ite_true, abs_zero]; positivity
  rcases le_or_gt t 1 with ht | ht
  · refine (h_Rhone_Analysis_abs_laplaceNullFunction_le_mul t).trans ?_
    have h1 : |t| * Real.sqrt |t| ≤ 1 := by
      rw [abs_of_pos h0]
      have : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht
      nlinarith [Real.sqrt_nonneg t]
    nlinarith
  · refine (h_Rhone_Analysis_abs_laplaceNullFunction_le h0).trans ?_
    have hs1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht.le
    have he : Real.exp (-(nullBeta ^ 2).re / t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := h_Rhone_Analysis_nullBeta_sq_re_pos
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
    have h2 : Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    nlinarith
end Rhone.Analysis
