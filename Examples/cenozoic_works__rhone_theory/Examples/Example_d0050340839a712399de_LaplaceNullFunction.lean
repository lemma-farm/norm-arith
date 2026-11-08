/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds
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
theorem abs_laplaceNullFunction_le {t : ℝ} (ht : 0 < t) :
    |laplaceNullFunction t| ≤
      ‖nullBeta‖ * (Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t)) := by
  have hst : 0 < t * Real.sqrt t := by positivity
  simp only [laplaceNullFunction, not_le.2 ht, ite_false, abs_mul]
  have h1 : |(nullBeta * cexp (-nullBeta ^ 2 / t)).re| ≤
      ‖nullBeta‖ * Real.exp (-(nullBeta ^ 2).re / t) := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_exp, Complex.div_ofReal_re, Complex.neg_re]
  have h2 : |Real.exp (-t / 8) / (t * Real.sqrt t)| ≤ 1 / (t * Real.sqrt t) := by
    rw [abs_of_nonneg (by positivity)]
    gcongr
    rw [Real.exp_le_one_iff]; linarith
  calc |(nullBeta * cexp (-nullBeta ^ 2 / t)).re| * |Real.exp (-t / 8) / (t * Real.sqrt t)|
      ≤ (‖nullBeta‖ * Real.exp (-(nullBeta ^ 2).re / t)) * (1 / (t * Real.sqrt t)) := by
        gcongr
    _ = _ := by ring
end Rhone.Analysis
