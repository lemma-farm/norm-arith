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
theorem nullBeta_sq :
    nullBeta ^ 2 = ((8 - Real.pi ^ 2 / 2 : ℝ) : ℂ) + ((4 * Real.pi : ℝ) : ℂ) * I := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [nullBeta, mul_pow, h2]
  push_cast
  ring_nf
  rw [I_sq]
  ring
theorem nullBeta_sq_re : (nullBeta ^ 2).re = 8 - Real.pi ^ 2 / 2 := by
  rw [nullBeta_sq, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re]
  ring
theorem nullBeta_sq_re_pos : 0 < (nullBeta ^ 2).re := by
  rw [nullBeta_sq_re]
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith
noncomputable def laplaceNullFunction (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
    (nullBeta * cexp (-nullBeta ^ 2 / t)).re * (Real.exp (-t / 8) / (t * Real.sqrt t))
theorem exp_neg_div_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Real.exp (-r / t) ≤ 6 * t ^ 3 / r ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (r / t) (by positivity) 3
  have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h
  rw [neg_div, Real.exp_neg]
  have hpos : 0 < (r / t) ^ 3 / 6 := by positivity
  calc (Real.exp (r / t))⁻¹ ≤ ((r / t) ^ 3 / 6)⁻¹ := by gcongr
    _ = 6 * t ^ 3 / r ^ 3 := by field_simp
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
theorem abs_laplaceNullFunction_le_mul (t : ℝ) :
    |laplaceNullFunction t| ≤
      6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (|t| * Real.sqrt |t|) := by
  have hr := nullBeta_sq_re_pos
  rcases le_or_gt t 0 with ht | ht
  · simp only [laplaceNullFunction, ht, ite_true, abs_zero]; positivity
  · refine (abs_laplaceNullFunction_le ht).trans ?_
    rw [abs_of_pos ht]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have he := exp_neg_div_le hr ht
    calc ‖nullBeta‖ * (Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t))
        ≤ ‖nullBeta‖ * (6 * t ^ 3 / (nullBeta ^ 2).re ^ 3 / (t * Real.sqrt t)) := by gcongr
      _ = 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (t * Real.sqrt t) := by
        field_simp
        have h2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
        have h3 := mul_le_mul_of_nonneg_left (le_of_eq h2) (norm_nonneg nullBeta)
        have h4 := mul_le_mul_of_nonneg_left (le_of_eq h2.symm) (norm_nonneg nullBeta)
        nlinarith [h3, h4, norm_nonneg nullBeta]
end Rhone.Analysis
