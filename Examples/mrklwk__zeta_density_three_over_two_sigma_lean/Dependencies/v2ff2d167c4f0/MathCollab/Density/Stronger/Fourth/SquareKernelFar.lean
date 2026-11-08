module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance and adaptation details: third_party/twelfth/SQUARE_KERNEL_SERIES_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.SquareNormalized
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex
open MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
theorem abs_polynomial_mul_exp_le_gaussian
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (D : ℝ) (m : ℕ) (u : ℝ) :
    (a+b*|u|)^m * Real.exp (D*|u|) ≤
      Real.exp ((m:ℝ)*a+((m:ℝ)*b+D)^2/4) * Real.exp (u^2) := by
  have hx : 0 ≤ a+b*|u| := by positivity
  have he : a+b*|u| ≤ Real.exp (a+b*|u|) := by
    linarith [Real.add_one_le_exp (a+b*|u|)]
  calc
    _ ≤ (Real.exp (a+b*|u|))^m * Real.exp (D*|u|) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx he m) (by positivity)
    _ = Real.exp ((m:ℝ)*(a+b*|u|)+D*|u|) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (((m:ℝ)*a+((m:ℝ)*b+D)^2/4)+u^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (|u|-((m:ℝ)*b+D)/2), sq_abs u]
    _ = _ := Real.exp_add _ _
theorem norm_vertical_shift_le {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ‖(c:ℂ)+(u:ℂ)*I‖ ≤ c+|u| := by
  simpa only [norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc] using
      norm_add_le (c:ℂ) ((u:ℂ)*I)
theorem vertical_shift_re_le_norm {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    c ≤ ‖(c:ℂ)+(u:ℂ)*I‖ := by
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, abs_of_nonneg hc] using
      Complex.abs_re_le_norm ((c:ℂ)+(u:ℂ)*I)
end MathCollab.Density.Stronger.Fourth
