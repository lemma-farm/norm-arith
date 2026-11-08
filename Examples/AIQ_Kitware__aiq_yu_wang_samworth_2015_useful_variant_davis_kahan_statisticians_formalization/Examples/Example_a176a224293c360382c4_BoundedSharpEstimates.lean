/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Riccati.BoundedEstimates
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Sharp contractive-branch majorant for bounded Riccati solutions

This leaf module solves the scalar quadratic inequality produced by the
interval/exterior Sylvester estimate.  On the contractive branch, the solution
norm is bounded by the smaller root of the Riccati majorant polynomial.

The result is stated in an algebraic square-root form.  This keeps the operator
argument independent of trigonometric normalization and exposes the exact
scalar endpoint needed by later continuation and branch-selection proofs.
-/
namespace TauCeti
namespace DavisKahanExt
open scoped InnerProductSpace
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]
omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A continuous linear map has a unit vector whose image norm is within every
positive amount below its operator norm. -/
theorem exists_unit_norm_apply_gt_sub
    (X : E0 →L[ℂ] E1) {ε : ℝ}
    (hε0 : 0 < ε) (hεt : ε < ‖X‖) :
    ∃ x : E0, ‖x‖ = 1 ∧ ‖X x‖ > ‖X‖ - ε := by
  by_contra h
  push Not at h
  have hop : ‖X‖ ≤ ‖X‖ - ε :=
    ContinuousLinearMap.opNorm_le_of_unit_norm
      (sub_nonneg.mpr hεt.le) (fun x hx => h x hx)
  linarith
/-- Squared adjoint-defect estimate for a normalized approximate singular pair.
The exact relation `X x = s y` fixes the cross term, while the operator norm
controls `X† y`. -/
theorem adjoint_defect_sq_le_of_normalized_pair
    (X : E0 →L[ℂ] E1) {x : E0} {y : E1} {s : ℝ}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hXx : X x = (s : ℂ) • y) :
    ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ^ 2 ≤
      2 * ‖X‖ * (‖X‖ - s) := by
  have hadj_norm : ‖X.adjoint y‖ ≤ ‖X‖ := by
    calc
      ‖X.adjoint y‖ ≤ ‖X.adjoint‖ * ‖y‖ := X.adjoint.le_opNorm y
      _ = ‖X‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map, hynorm, mul_one]
  have hadj_sq : ‖X.adjoint y‖ ^ 2 ≤ ‖X‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg X)).2 hadj_norm
  have hinner : RCLike.re ⟪X.adjoint y, x⟫_ℂ = s := by
    rw [ContinuousLinearMap.adjoint_inner_left, hXx, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hynorm]
    norm_num
  have hinner_scaled :
      RCLike.re ⟪X.adjoint y, (‖X‖ : ℂ) • x⟫_ℂ = ‖X‖ * s := by
    rw [inner_smul_right, ← Complex.real_smul, RCLike.smul_re, hinner]
  simp only [norm_sub_sq (𝕜 := ℂ), hinner_scaled, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg X), hxnorm, mul_one]
  nlinarith
/-- A near norm-attaining vector and its normalized image form an approximate
singular pair.  The adjoint defect is bounded by the square-root error naturally
produced by the polarization identity. -/
theorem exists_near_singular_pair
    (X : E0 →L[ℂ] E1) {ε : ℝ}
    (hε0 : 0 < ε) (hεt : ε < ‖X‖) :
    ∃ (x : E0) (y : E1) (s : ℝ),
      ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      ‖X‖ - ε < s ∧ s ≤ ‖X‖ ∧
      X x = (s : ℂ) • y ∧
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ≤
        Real.sqrt (2 * ‖X‖ * ε) := by
  obtain ⟨x, hxnorm, hxnear⟩ := exists_unit_norm_apply_gt_sub X hε0 hεt
  set s : ℝ := ‖X x‖ with hs
  have hspos : 0 < s := by
    have hsubpos : 0 < ‖X‖ - ε := sub_pos.mpr hεt
    exact hsubpos.trans hxnear
  set y : E1 := (((s⁻¹ : ℝ) : ℂ) • X x) with hy
  have hynorm : ‖y‖ = 1 := by
    rw [hy, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hspos.le), ← hs,
      inv_mul_cancel₀ hspos.ne']
  have hXx : X x = (s : ℂ) • y := by
    rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hspos.ne',
      Complex.ofReal_one, one_smul]
  have hsle : s ≤ ‖X‖ := by
    have h := X.le_opNorm x
    rw [hxnorm, mul_one] at h
    simpa [hs] using h
  have hdef_sq :=
    adjoint_defect_sq_le_of_normalized_pair X hxnorm hynorm hXx
  have hgap : ‖X‖ - s < ε := by linarith
  have hrad_le :
      2 * ‖X‖ * (‖X‖ - s) ≤ 2 * ‖X‖ * ε := by
    exact mul_le_mul_of_nonneg_left hgap.le
      (mul_nonneg (by norm_num) (norm_nonneg X))
  have hdef_sq' :
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ^ 2 ≤ 2 * ‖X‖ * ε :=
    hdef_sq.trans hrad_le
  have hrad0 : 0 ≤ 2 * ‖X‖ * ε :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg X)) hε0.le
  have hdef :
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ≤ Real.sqrt (2 * ‖X‖ * ε) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hrad0]
    exact hdef_sq'
  exact ⟨x, y, s, hxnorm, hynorm, hxnear, hsle, hXx, hdef⟩
end DavisKahanExt
end TauCeti