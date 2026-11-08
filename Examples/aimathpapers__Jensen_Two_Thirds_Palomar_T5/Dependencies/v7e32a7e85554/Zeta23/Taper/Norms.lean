/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.v7e32a7e85554.Zeta23.Taper.Basic
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
namespace Taper
section Norms
variable {ϱ : ℝ → ℝ} {L w : ℝ}
private lemma rho_differentiable (hϱ : TaperProfile ϱ) : Differentiable ℝ ϱ :=
  hϱ.contDiff.differentiable (by norm_num)
private lemma derivRho_zero_left (hϱ : TaperProfile ϱ) {x : ℝ} (hx : x < 0) : deriv ϱ x = 0 := by
  have hev : ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with v hv
    exact hϱ.eq_zero v (le_of_lt hv)
  rw [hev.deriv_eq]
  simp
/-- deriv ϱ vanishes right of 1 (ϱ is locally 1 there). -/
private lemma derivRho_zero_right (hϱ : TaperProfile ϱ) {x : ℝ} (hx : 1 < x) : deriv ϱ x = 0 := by
  have hev : ϱ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with v hv
    exact hϱ.eq_one v (le_of_lt hv)
  rw [hev.deriv_eq]
  simp
private lemma derivRho_continuous (hϱ : TaperProfile ϱ) : Continuous (deriv ϱ) :=
  hϱ.contDiff.continuous_deriv (by norm_num)
private lemma bddAbove_abs_derivRho (hϱ : TaperProfile ϱ) :
    BddAbove (Set.range fun x => |deriv ϱ x|) := by
  have hcs : HasCompactSupport (deriv ϱ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      fun x hx => ?_
    rw [Function.mem_support] at hx
    by_contra h
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact hx (derivRho_zero_left hϱ h)
    · exact hx (derivRho_zero_right hϱ h)
  exact (derivRho_continuous hϱ).abs.bddAbove_range_of_hasCompactSupport
    (hcs.comp_left (g := fun t => |t|) abs_zero)
private lemma abs_derivRho_le (hϱ : TaperProfile ϱ) (y : ℝ) : |deriv ϱ y| ≤ supDeriv ϱ :=
  le_ciSup (bddAbove_abs_derivRho hϱ) y
private lemma l1Deriv2_nonneg (ϱ : ℝ → ℝ) : 0 ≤ l1Deriv2 ϱ :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _
theorem four_le_cRho (hϱ : TaperProfile ϱ) : 4 ≤ cRho ϱ := by
  have hl1 := l1Deriv2_nonneg ϱ
  have hftc : ∫ y in (0 : ℝ)..1, deriv ϱ y = 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => rho_differentiable hϱ x)
      ((derivRho_continuous hϱ).intervalIntegrable _ _)]
    rw [hϱ.eq_one 1 le_rfl, hϱ.eq_zero 0 le_rfl]
    ring
  have hone : (1 : ℝ) ≤ supDeriv ϱ := by
    have hle : ∫ y in (0 : ℝ)..1, deriv ϱ y ≤ ∫ y in (0 : ℝ)..1, supDeriv ϱ := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((derivRho_continuous hϱ).intervalIntegrable _ _) intervalIntegrable_const
        fun x _ => ?_
      exact le_trans (le_abs_self _) (abs_derivRho_le hϱ x)
    rw [hftc] at hle
    simpa using hle
  rw [cRho_eq]
  linarith
end Norms
/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/
section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}
private lemma L_pos (hw : 0 < w) (hwL : 2 * w ≤ L) : (0 : ℝ) < L := by linarith
private lemma integrable_phi_pow (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun u => phi ϱ L w u ^ n) :=
  ((phi_continuous hϱ hw hwL).pow n).integrable_of_hasCompactSupport
    ((phi_hasCompactSupport hϱ hw).comp_left (g := (· ^ n)) (by simp [zero_pow hn.ne']))
theorem bConst_le_aConst (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    bConst ϱ L w ≤ aConst ϱ L w := by
  have hL := L_pos hw hwL
  unfold bConst aConst
  have hmono : ∫ u : ℝ, phi ϱ L w u ^ 4 ≤ ∫ u : ℝ, phi ϱ L w u ^ 2 := by
    refine MeasureTheory.integral_mono (integrable_phi_pow hϱ hw hwL (by norm_num))
      (integrable_phi_pow hϱ hw hwL (by norm_num)) fun u => ?_
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    have h1 := phi_le_one hϱ (L := L) (w := w) u
    have hp2 : phi ϱ L w u ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    have hp2n : (0 : ℝ) ≤ phi ϱ L w u ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hp2 hp2n]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)
theorem aConst_le_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    aConst ϱ L w ≤ 1 := by
  have hL := L_pos hw hwL
  unfold aConst
  have hsupp : ∀ u ∉ Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2 = 0 := by
    intro u hu
    have : phi ϱ L w u = 0 := by
      apply phi_eq_zero hϱ hw
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · calc L / 2 ≤ -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 ≤ u := by linarith
          _ ≤ |u| := le_abs_self u
    rw [this]
    ring
  have heq : ∫ u : ℝ, phi ϱ L w u ^ 2 = ∫ u in Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have hle : ∫ u in Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2
      ≤ ∫ u in Icc (-(L / 2)) (L / 2), (1 : ℝ) := by
    refine MeasureTheory.setIntegral_mono_on
      ((integrable_phi_pow hϱ hw hwL (by norm_num)).integrableOn)
      (MeasureTheory.integrableOn_const (by simp)) measurableSet_Icc fun u _ => ?_
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    have h1 := phi_le_one hϱ (L := L) (w := w) u
    nlinarith
  have hvol : ∫ u in Icc (-(L / 2)) (L / 2), (1 : ℝ) = L := by
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    rw [smul_eq_mul, mul_one]
    ring
  calc L⁻¹ * ∫ u : ℝ, phi ϱ L w u ^ 2 ≤ L⁻¹ * L := by
        rw [heq]
        exact mul_le_mul_of_nonneg_left (le_trans hle (le_of_eq hvol)) (by positivity)
    _ = 1 := inv_mul_cancel₀ hL.ne'
end AB
end Taper
end Zeta23
