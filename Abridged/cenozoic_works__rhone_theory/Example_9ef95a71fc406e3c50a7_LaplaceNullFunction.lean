module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_9ef95a71fc406e3c50a7_LaplaceNullFunction ====
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
theorem integral_laplace_levy_kernel {β : ℂ} (hβ : 0 < β.re) (hβ2 : 0 < (β ^ 2).re) {c : ℝ}
    (hc : 0 ≤ c) 
    (h_Rhone_Analysis_integral_exp_neg_div_div_sq : ∀ {a : ℝ}, 0 < a → ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-a / t) / t ^ 2 = 1 / a)
    (h_Rhone_Analysis_integral_cexp_mul_I_div_sq_add_sq : ∀ {β : ℂ},
      0 < β.re →
        0 < (β ^ 2).re →
          ∀ (x : ℝ),
            ∫ (y : ℝ), Complex.exp ((↑(y * x) : ℂ) * Complex.I) * (1 / (β ^ 2 + (↑y : ℂ) ^ 2)) =
              (↑Real.pi : ℂ) / β * Complex.exp (-β * (↑|x| : ℂ)))
    (h_Rhone_Analysis_integral_cexp_neg_div_div_sq : ∀ {w : ℂ},
      0 < w.re →
        MeasureTheory.IntegrableOn (fun (t : ℝ) ↦ Complex.exp (-w / (↑t : ℂ)) / (↑t : ℂ) ^ 2)
            (Set.Ioi 0) MeasureTheory.MeasureSpace.volume ∧
          ∫ (t : ℝ) in Set.Ioi 0, Complex.exp (-w / (↑t : ℂ)) / (↑t : ℂ) ^ 2 = 1 / w)
    (h_Rhone_Analysis_exp_neg_sq_mul_eq_integral : ∀ {t : ℝ},
      0 < t →
        ∀ (c : ℝ),
          (↑(Real.exp (-c ^ 2 * t)) : ℂ) =
            (↑(√(Real.pi * t))⁻¹ : ℂ) *
              ∫ (y : ℝ),
                Complex.exp (Complex.I * (↑(2 * c) : ℂ) * (↑y : ℂ)) *
                  Complex.exp (-(↑t : ℂ)⁻¹ * (↑y : ℂ) ^ 2))
    :
    ∫ t in Ioi (0 : ℝ), β * cexp (-β ^ 2 / t) *
        ((Real.exp (-c ^ 2 * t) / (t * Real.sqrt t) : ℝ) : ℂ) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * cexp (-2 * c * β) := by
  have hβ0 : β ≠ 0 := by intro h; simp [h] at hβ
  set r := (β ^ 2).re
  let F : ℝ → ℝ → ℂ := fun t y =>
    β * cexp (I * ((2 * c : ℝ) : ℂ) * y) * (cexp (-(β ^ 2 + (y : ℂ) ^ 2) / t) / (t : ℂ) ^ 2)
  have hw : ∀ y : ℝ, 0 < (β ^ 2 + (y : ℂ) ^ 2).re := by
    intro y; simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re]; positivity
  have hsqπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), β * cexp (-β ^ 2 / t) *
      ((Real.exp (-c ^ 2 * t) / (t * Real.sqrt t) : ℝ) : ℂ) =
      ((Real.sqrt Real.pi)⁻¹ : ℝ) * ∫ y : ℝ, F t y := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hst : Real.sqrt t ≠ 0 := by positivity
    have hstC : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hst
    have hsπC : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqπ
    have hF : ∀ y : ℝ, F t y = (β * cexp (-β ^ 2 / t) / (t : ℂ) ^ 2) *
        (cexp (I * ((2 * c : ℝ) : ℂ) * y) * cexp (-(t : ℂ)⁻¹ * (y : ℂ) ^ 2)) := by
      intro y
      simp only [F]
      have : cexp (-(β ^ 2 + (y : ℂ) ^ 2) / t) =
          cexp (-β ^ 2 / t) * cexp (-(t : ℂ)⁻¹ * (y : ℂ) ^ 2) := by
        rw [← Complex.exp_add]; congr 1; field_simp; ring
      rw [this]; field_simp
    simp_rw [hF]
    rw [integral_const_mul, Complex.ofReal_div, h_Rhone_Analysis_exp_neg_sq_mul_eq_integral ht c]
    have hsq : Real.sqrt (Real.pi * t) = Real.sqrt Real.pi * Real.sqrt t :=
      Real.sqrt_mul Real.pi_pos.le t
    have htt : ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) = t := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
    rw [hsq]
    push_cast
    field_simp
    rw [show ((Real.sqrt t : ℝ) : ℂ) ^ 2 = t by rw [sq, htt]]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [F, Function.uncurry_def]
    fun_prop
  have hnorm : ∀ t y : ℝ, ‖F t y‖ = ‖β‖ * (Real.exp (-(r + y ^ 2) / t) / t ^ 2) := by
    intro t y
    simp only [F, norm_mul, norm_div, Complex.norm_exp, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have h1 : (I * ((2 * c : ℝ) : ℂ) * (y : ℂ)).re = 0 := by simp
    have h2 : (-(β ^ 2 + (y : ℂ) ^ 2) / (t : ℂ)).re = -(r + y ^ 2) / t := by
      rw [Complex.div_ofReal_re]
      simp [r, ← Complex.ofReal_pow]
    rw [h1, h2, Real.exp_zero, mul_one]
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · change Integrable (fun t => F t y) (volume.restrict (Ioi 0))
      exact (h_Rhone_Analysis_integral_cexp_neg_div_div_sq (hw y)).1.const_mul
        (β * cexp (I * ((2 * c : ℝ) : ℂ) * y))
    · have hval : ∀ y : ℝ, ∫ t in Ioi (0 : ℝ), ‖F t y‖ = ‖β‖ * (r + y ^ 2)⁻¹ := by
        intro y
        simp_rw [hnorm]
        rw [integral_const_mul, h_Rhone_Analysis_integral_exp_neg_div_div_sq (by positivity), one_div]
      change Integrable (fun y : ℝ => ∫ t in Ioi (0 : ℝ), ‖F t y‖) volume
      simp_rw [hval]
      set m := min r 1
      have hm : 0 < m := lt_min hβ2 one_pos
      refine (integrable_inv_one_add_sq.const_mul (‖β‖ / m)).mono' ?_ ?_
      · exact (Continuous.aestronglyMeasurable (by
          refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y => ?_)
          positivity))
      · filter_upwards with y
        have h1 : m * (1 + y ^ 2) ≤ r + y ^ 2 := by
          have := min_le_left r 1
          have := min_le_right r 1
          nlinarith [sq_nonneg y]
        have hpos : 0 < m * (1 + y ^ 2) := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc ‖β‖ * (r + y ^ 2)⁻¹ ≤ ‖β‖ * (m * (1 + y ^ 2))⁻¹ := by
              gcongr
          _ = ‖β‖ / m * (1 + y ^ 2)⁻¹ := by field_simp
  rw [integral_integral_swap hint]
  have hinner : ∀ y : ℝ, ∫ t in Ioi (0 : ℝ), F t y =
      β * (cexp (↑(y * (2 * c)) * I) * (1 / (β ^ 2 + (y : ℂ) ^ 2))) := by
    intro y
    simp only [F]
    rw [integral_const_mul, (h_Rhone_Analysis_integral_cexp_neg_div_div_sq (hw y)).2]
    have : cexp (I * ((2 * c : ℝ) : ℂ) * y) = cexp (↑(y * (2 * c)) * I) := by
      congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hinner]
  rw [integral_const_mul, h_Rhone_Analysis_integral_cexp_mul_I_div_sq_add_sq hβ hβ2,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)]
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) = Real.pi := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hsπC : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqπ
  push_cast
  field_simp
  rw [← hπ]
  ring_nf
end Rhone.Analysis
