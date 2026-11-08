/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundBadPart
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveLevelIntegration
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Calderón--Zygmund atoms on magnitude levels

This file isolates the algebraic and measure-theoretic facts about the atoms

`1_I (f 1_{F_k} - average_I (f 1_{F_k}))`

used in the positive-endpoint argument.  It does not assert the existence of
a Calderón--Zygmund decomposition: the interval (or a disjoint family of
intervals) is supplied explicitly.
-/
open MeasureTheory Set
open scoped ENNReal BigOperators Function
namespace QuadraticCarleson
namespace CalderonZygmundLevelAtoms
open PositiveEndpointOptimization PositiveLevelIntegration
set_option autoImplicit false
noncomputable section
/-- The part of `f` lying in the magnitude band `F_k`. -/
def levelRestricted (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  (magnitudeLevelSet A f k).indicator f
/-- The average of the level-restricted function over the centered interval. -/
def levelAverage (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℂ :=
  ⨍ x in centeredInterval z R, levelRestricted A f k x
/-- The level atom attached to a centered interval. -/
def levelAtom (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ → ℂ :=
  (centeredInterval z R).indicator
    (fun x ↦ levelRestricted A f k x - levelAverage A f k z R)
@[simp] theorem volume_centeredInterval (z R : ℝ) :
    volume (centeredInterval z R) = ENNReal.ofReal R := by
  simp [centeredInterval, Real.volume_Ico]
theorem volume_centeredInterval_lt_top (z R : ℝ) :
    volume (centeredInterval z R) < ∞ := by
  rw [volume_centeredInterval]
  exact ENNReal.ofReal_lt_top
theorem volumeReal_centeredInterval {z R : ℝ} (hR : 0 ≤ R) :
    volume.real (centeredInterval z R) = R := by
  simp [Measure.real, volume_centeredInterval, hR]
theorem levelRestricted_apply_of_mem {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {x : ℝ} (hx : x ∈ magnitudeLevelSet A f k) :
    levelRestricted A f k x = f x := by
  simp [levelRestricted, hx]
theorem levelRestricted_apply_of_not_mem {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {x : ℝ} (hx : x ∉ magnitudeLevelSet A f k) :
    levelRestricted A f k x = 0 := by
  simp [levelRestricted, hx]
/-- The upper endpoint in the definition of `F_k` is an exact pointwise bound. -/
theorem norm_levelRestricted_le {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) (x : ℝ) :
    ‖levelRestricted A f k x‖ ≤ A k := by
  by_cases hx : x ∈ magnitudeLevelSet A f k
  · rw [levelRestricted_apply_of_mem hx]
    by_cases hk : k = 0
    · simp only [mem_magnitudeLevelSet, InMagnitudeLevel, hk, ↓reduceIte] at hx
      simpa [hk] using hx.2
    · simp only [mem_magnitudeLevelSet, InMagnitudeLevel, hk, ↓reduceIte] at hx
      exact hx.2
  · rw [levelRestricted_apply_of_not_mem hx, norm_zero]
    exact hAk
theorem norm_levelAverage_le {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    ‖levelAverage A f k z R‖ ≤ A k := by
  have hI : volume (centeredInterval z R) < ∞ := volume_centeredInterval_lt_top z R
  have hInt :
      ‖∫ x in centeredInterval z R, levelRestricted A f k x‖ ≤
        A k * volume.real (centeredInterval z R) :=
    norm_setIntegral_le_of_norm_le_const_ae hI
      (Filter.Eventually.of_forall fun x ↦ norm_levelRestricted_le hAk x)
  rw [levelAverage, setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 measureReal_nonneg)]
  calc
    (volume.real (centeredInterval z R))⁻¹ *
          ‖∫ x in centeredInterval z R, levelRestricted A f k x‖ ≤
        (volume.real (centeredInterval z R))⁻¹ *
          (A k * volume.real (centeredInterval z R)) :=
      mul_le_mul_of_nonneg_left hInt (inv_nonneg.2 measureReal_nonneg)
    _ = A k := by
      rw [volumeReal_centeredInterval hR.le]
      field_simp
theorem norm_levelAtom_le_two_mul {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖levelAtom A f k z R x‖ ≤ 2 * A k := by
  by_cases hx : x ∈ centeredInterval z R
  · rw [levelAtom, indicator_of_mem hx]
    calc
      ‖levelRestricted A f k x - levelAverage A f k z R‖ ≤
          ‖levelRestricted A f k x‖ + ‖levelAverage A f k z R‖ := norm_sub_le _ _
      _ ≤ A k + A k := add_le_add (norm_levelRestricted_le hAk x)
        (norm_levelAverage_le hAk hR)
      _ = 2 * A k := by ring
  · rw [levelAtom, indicator_of_notMem hx, norm_zero]
    exact mul_nonneg (by norm_num) hAk
theorem levelAtom_eq_zero_of_not_mem {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {z R x : ℝ} (hx : x ∉ centeredInterval z R) :
    levelAtom A f k z R x = 0 := by
  simp [levelAtom, hx]
end
end CalderonZygmundLevelAtoms
end QuadraticCarleson
