/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.SHF.Moments.PairBlockCompositionVariance
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.PairedLocalCLT
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Local central limit estimates for pair-block increments -/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter
private theorem ctGauss_one_eval (t : ℝ) (x : ℤ) :
    LatticeProb.ContinuousTime.ctGauss 1 t ![x] =
      (Real.sqrt (2 * Real.pi * t))⁻¹ *
        Real.exp (-(x : ℝ) ^ 2 / (2 * t)) := by
  simp [LatticeProb.ContinuousTime.ctGauss,
    LatticeProb.ContinuousTime.lineGauss]
private theorem ctGauss_one_return_scaled (m : ℕ) (hm : 0 < m) :
    Real.sqrt (m : ℝ) *
      (2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![(0 : ℤ)]) =
        (Real.sqrt Real.pi)⁻¹ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hroot2 : Real.sqrt (2 * Real.pi * (2 * (m : ℝ))) =
      2 * Real.sqrt Real.pi * Real.sqrt (m : ℝ) := by
    rw [show 2 * Real.pi * (2 * (m : ℝ)) = 4 * (Real.pi * (m : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul (by positivity)]
    ring
  rw [ctGauss_one_eval, hroot2]
  norm_num
  field_simp [hmR.ne', Real.pi_pos.ne',
    (Real.sqrt_pos.mpr hmR).ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']
private theorem ctGauss_one_pair_profile (m : ℕ) (hm : 0 < m) (x : ℤ) :
    Real.sqrt (m : ℝ) *
        ((2 * LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x]) ^ 2 /
          (2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![(0 : ℤ)])) =
      2 / Real.sqrt Real.pi * Real.exp (-(x : ℝ) ^ 2 / (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpi : 0 < Real.pi := Real.pi_pos
  have hroot : Real.sqrt (2 * Real.pi * (m : ℝ)) =
      Real.sqrt 2 * Real.sqrt Real.pi * Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hroot2 : Real.sqrt (2 * Real.pi * (2 * (m : ℝ))) =
      2 * Real.sqrt Real.pi * Real.sqrt (m : ℝ) := by
    rw [show 2 * Real.pi * (2 * (m : ℝ)) = 4 * (Real.pi * (m : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul (by positivity)]
    ring
  rw [ctGauss_one_eval, ctGauss_one_eval]
  have hexp :
      Real.exp (-(x : ℝ) ^ 2 / (2 * (m : ℝ))) ^ 2 =
        Real.exp (-(x : ℝ) ^ 2 / (m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  rw [hroot, hroot2, mul_pow, mul_pow, hexp]
  norm_num
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsqrtm : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  have hsqrtpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  field_simp [hmR.ne', hpi.ne', hsqrtm, hsqrtpi]
  rw [pow_two, hsqrt2]
  ring
private theorem abs_sq_ratio_sub_le {A B D E : ℝ}
    (hD : 1 / 4 ≤ D) (hE : 1 / 2 ≤ E)
    (hAlo : -2 ≤ A) (hAhi : A ≤ 2)
    (hBlo : -2 ≤ B) (hBhi : B ≤ 2) :
    |A ^ 2 / D - B ^ 2 / E| ≤
      16 * |A - B| + 32 * |D - E| := by
  have hDpos : 0 < D := by linarith
  have hEpos : 0 < E := by linarith
  have hprod : 1 / 8 ≤ D * E := by
    have h := mul_le_mul hD hE (by norm_num) (by positivity)
    nlinarith
  have hprodpos : 0 < D * E := mul_pos hDpos hEpos
  have hAabs : |A| ≤ 2 := abs_le.mpr ⟨hAlo, hAhi⟩
  have hBabs : |B| ≤ 2 := abs_le.mpr ⟨hBlo, hBhi⟩
  have hsum : |A + B| ≤ 4 := by
    calc
      |A + B| ≤ |A| + |B| := abs_add_le _ _
      _ ≤ 4 := by linarith
  have hAsq : A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
  have hfirst : |(A ^ 2 - B ^ 2) / D| ≤ 16 * |A - B| := by
    rw [hAsq, abs_div, abs_of_pos hDpos, abs_mul]
    have hrecip : 4 / D ≤ 16 := (div_le_iff₀ hDpos).2 (by nlinarith)
    calc
      |A - B| * |A + B| / D ≤ |A - B| * 4 / D := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        · exact hDpos.le
      _ = |A - B| * (4 / D) := by ring
      _ ≤ |A - B| * 16 := mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
      _ = 16 * |A - B| := by ring
  have hBsq : B ^ 2 ≤ 4 := by nlinarith [hBabs]
  have hcoef : B ^ 2 / (D * E) ≤ 32 := by
    apply (div_le_iff₀ hprodpos).2
    nlinarith [hprod]
  have hsecond : |B ^ 2 * (E - D) / (D * E)| ≤ 32 * |D - E| := by
    rw [abs_div, abs_of_pos hprodpos, abs_mul, abs_of_nonneg (sq_nonneg B)]
    have hrev : |E - D| = |D - E| := by rw [show E - D = -(D - E) by ring, abs_neg]
    rw [hrev]
    calc
      B ^ 2 * |D - E| / (D * E) =
          (B ^ 2 / (D * E)) * |D - E| := by ring
      _ ≤ 32 * |D - E| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
  have hidentity : A ^ 2 / D - B ^ 2 / E =
      (A ^ 2 - B ^ 2) / D + B ^ 2 * (E - D) / (D * E) := by
    field_simp [hDpos.ne', hEpos.ne']
    ring
  calc
    |A ^ 2 / D - B ^ 2 / E| =
        |(A ^ 2 - B ^ 2) / D + B ^ 2 * (E - D) / (D * E)| := by rw [hidentity]
    _ ≤ |(A ^ 2 - B ^ 2) / D| + |B ^ 2 * (E - D) / (D * E)| := abs_add_le _ _
    _ ≤ 16 * |A - B| + 32 * |D - E| := add_le_add hfirst hsecond
/-- The one-dimensional parity local CLT, rescaled to the natural
`sqrt(n)` normalization. The error is uniformly `O(1/n)` over every site of
the accessible parity class. -/
theorem exists_srwHeat_one_scaled_parity_error :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : LatticeProb.Site 1,
      ((LatticeProb.graphNorm x : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) →
        |Real.sqrt (n : ℝ) * LatticeProb.srwHeat 1 n x -
          Real.sqrt (n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x|
          ≤ C / (n : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ :=
    LatticeProb.LocalCLT.exists_abs_srwHeat_sub_le (d := 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro n hn x hpar
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hlocal' := hlocal n hn x hpar
  have hlocal'' :
      |LatticeProb.srwHeat 1 n x -
        2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x| ≤
        C * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    convert hlocal' using 1
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hlocal'' hsqrt
  have habs :
      |Real.sqrt (n : ℝ) * LatticeProb.srwHeat 1 n x -
        Real.sqrt (n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x| =
        Real.sqrt (n : ℝ) *
          |LatticeProb.srwHeat 1 n x -
            2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x| := by
    rw [show Real.sqrt (n : ℝ) * LatticeProb.srwHeat 1 n x -
        Real.sqrt (n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x =
          Real.sqrt (n : ℝ) * (LatticeProb.srwHeat 1 n x -
            2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x) by ring,
      abs_mul, abs_of_nonneg hsqrt]
  rw [habs]
  have hpow : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / (n : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnR]
    norm_num
    rw [Real.rpow_neg_one]
  calc
    _ ≤ Real.sqrt (n : ℝ) * (C * (n : ℝ) ^ (-(3 / 2 : ℝ))) := hmul
    _ = C / (n : ℝ) := by calc
      _ = C * (Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
      _ = C / (n : ℝ) := by rw [hpow]; field_simp [hnR.ne']
private theorem srwHeat_one_return_scaled_error (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ n : ℕ, 1 ≤ n → ∀ x : LatticeProb.Site 1,
      ((LatticeProb.graphNorm x : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) →
        |Real.sqrt (n : ℝ) * LatticeProb.srwHeat 1 n x -
          Real.sqrt (n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x|
          ≤ C / (n : ℝ))
    (m : ℕ) (hm : 1 ≤ m) :
    |Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] -
      Real.sqrt (m : ℝ) * 2 *
        LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![(0 : ℤ)]| ≤ C / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hroot2 : Real.sqrt (2 * (m : ℝ)) = Real.sqrt 2 * Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hroot2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hq : (Real.sqrt 2)⁻¹ ≤ 1 := by
    have hroot2ge : 1 ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact (inv_le_one₀ hroot2pos).2 hroot2ge
  have h0par :
      ((LatticeProb.graphNorm (![0] : LatticeProb.Site 1) : ℕ) : ZMod 2) =
        (((2 * m : ℕ) : ℕ) : ZMod 2) := by
    rw [LatticeProb.graphNorm_one]
    simp only [Int.natAbs_zero, Nat.cast_zero]
    rw [Nat.cast_mul]
    have hcast2 : (↑(2 : ℕ) : ZMod 2) = 0 := by decide
    rw [hcast2]
    simp
  have hlarge := hlocal (2 * m) (by omega) ![0] h0par
  have hscaleWalk :
      Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] =
        (Real.sqrt 2)⁻¹ *
          (Real.sqrt (2 * (m : ℝ)) * LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)]) := by
    rw [hroot2]
    field_simp [hroot2pos.ne']
  have hscaleGauss :
      Real.sqrt (m : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1
          (2 * (m : ℝ)) ![(0 : ℤ)] =
        (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * (m : ℝ)) * 2 *
          LatticeProb.ContinuousTime.ctGauss 1
            (2 * (m : ℝ)) ![(0 : ℤ)]) := by
    rw [hroot2]
    field_simp [hroot2pos.ne']
  rw [hscaleWalk, hscaleGauss]
  have habs :
      |(Real.sqrt 2)⁻¹ * (Real.sqrt (2 * (m : ℝ)) *
            LatticeProb.srwHeat 1 (2 * m) ![0]) -
        (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * (m : ℝ)) * 2 *
            LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0])| =
        (Real.sqrt 2)⁻¹ * |Real.sqrt (2 * (m : ℝ)) *
            LatticeProb.srwHeat 1 (2 * m) ![0] -
          Real.sqrt (2 * (m : ℝ)) * 2 *
            LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0]| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [habs]
  calc
    _ ≤ 1 * |Real.sqrt (2 * (m : ℝ)) * LatticeProb.srwHeat 1 (2 * m) ![0] -
        Real.sqrt (2 * (m : ℝ)) * 2 *
          LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0]| :=
      mul_le_mul_of_nonneg_right hq (abs_nonneg _)
    _ ≤ C / ((2 * m : ℕ) : ℝ) := by
      simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using hlarge
    _ ≤ C / (m : ℝ) := by
      have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hcast]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ)) hmR]
      nlinarith [hC, hmR]
private theorem graphNorm_two_mul_sub_parity (m j : ℕ) :
    ((LatticeProb.graphNorm
        (![2 * (j : ℤ) - (m : ℤ)] : LatticeProb.Site 1) : ℕ) : ZMod 2) =
      ((m : ℕ) : ZMod 2) := by
  rw [LatticeProb.graphNorm_one, LatticeProb.natAbs_cast_zmod]
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2]
  simp [ZMod.neg_eq_self_mod_two]
private theorem srwHeat_one_scaled_bounds (m : ℕ) (hm : 1 ≤ m)
    (x : ℤ) :
    0 ≤ Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 m ![x] ∧
      Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 m ![x] ≤ 2 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hsqrtm : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hheat0 : 0 ≤ LatticeProb.srwHeat 1 m ![x] := LatticeProb.srwHeat_nonneg m ![x]
  have hroot : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hrootpos : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hratio : Real.sqrt (m : ℝ) / Real.sqrt ((m : ℝ) + 1) ≤ 1 :=
    (div_le_one hrootpos).2 hroot
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hupper : Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 m ![x] ≤ 2 := by
    calc
      Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 m ![x] ≤
          Real.sqrt (m : ℝ) * (Real.sqrt 2 / Real.sqrt ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (LatticeProb.srwHeat_one_le m x) hsqrtm
      _ = Real.sqrt 2 * (Real.sqrt (m : ℝ) / Real.sqrt ((m : ℝ) + 1)) := by ring
      _ ≤ Real.sqrt 2 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hratio (Real.sqrt_nonneg _))
      _ ≤ 2 := hsqrt2
  exact ⟨mul_nonneg hsqrtm hheat0, hupper⟩
private theorem ctGauss_one_scaled_bounds (m : ℕ) (hm : 1 ≤ m)
    (x : ℤ) :
    0 ≤ Real.sqrt (m : ℝ) * 2 *
        LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x] ∧
      Real.sqrt (m : ℝ) * 2 *
        LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x] ≤ 2 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hsqrtm : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hrootpos : 0 < Real.sqrt (2 * Real.pi * (m : ℝ)) := by positivity
  have hrootBound : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * Real.pi * (m : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three, hmR]
  have hratio : 0 ≤ Real.sqrt (m : ℝ) / Real.sqrt (2 * Real.pi * (m : ℝ)) ∧
      Real.sqrt (m : ℝ) / Real.sqrt (2 * Real.pi * (m : ℝ)) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hrootpos).2 hrootBound
  have harg : -(x : ℝ) ^ 2 / (2 * (m : ℝ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (x : ℝ)]
    · positivity
  have hexp := Real.exp_le_one_iff.mpr harg
  have hexp0 : 0 ≤ Real.exp (-(x : ℝ) ^ 2 / (2 * (m : ℝ))) := Real.exp_nonneg _
  have hform :
      Real.sqrt (m : ℝ) * 2 *
        LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x] =
      2 * (Real.sqrt (m : ℝ) / Real.sqrt (2 * Real.pi * (m : ℝ))) *
        Real.exp (-(x : ℝ) ^ 2 / (2 * (m : ℝ))) := by
    rw [ctGauss_one_eval]
    ring
  rw [hform]
  constructor
  · positivity
  · have hprod :
        (Real.sqrt (m : ℝ) / Real.sqrt (2 * Real.pi * (m : ℝ))) *
            Real.exp (-(x : ℝ) ^ 2 / (2 * (m : ℝ))) ≤ 1 := by
      calc
        _ ≤ 1 * Real.exp (-(x : ℝ) ^ 2 / (2 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_right hratio.2 hexp0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hexp (by norm_num)
        _ = 1 := by norm_num
    calc
      _ = 2 * ((Real.sqrt (m : ℝ) / Real.sqrt (2 * Real.pi * (m : ℝ))) *
            Real.exp (-(x : ℝ) ^ 2 / (2 * (m : ℝ)))) := by ring
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 2 := by norm_num
/-- The scaled squared-binomial law of one composition block has a uniform
`O(1/m)` local Gaussian error over all accessible marks. -/
theorem exists_hypergeometricWeight_localGaussian_error :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ k : ℕ, k ≤ m →
        |Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k -
          2 / Real.sqrt Real.pi * Real.exp
            (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))| ≤ C / (m : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := exists_srwHeat_one_scaled_parity_error
  have hlarge1 : ∀ᶠ m : ℕ in atTop, 4 * C < (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (4 * C)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hlarge1
  refine ⟨48 * C, by positivity, m₀, ?_⟩
  intro m hm₀m
  have hmLarge1 : 4 * C < (m : ℝ) := hm₀ m hm₀m
  intro k hk
  have hmReal : 0 < (m : ℝ) := by linarith [hC, hmLarge1]
  have hmPos : 0 < m := by exact_mod_cast hmReal
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmPos)
  let x : ℤ := 2 * (k : ℤ) - (m : ℤ)
  let a : ℝ := LatticeProb.srwHeat 1 m ![x]
  let d : ℝ := LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)]
  let e : ℝ := 2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![(0 : ℤ)]
  let A : ℝ := Real.sqrt (m : ℝ) * a
  let B : ℝ := Real.sqrt (m : ℝ) * 2 *
    LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x]
  let D : ℝ := Real.sqrt (m : ℝ) * d
  let E : ℝ := Real.sqrt (m : ℝ) * e
  have hxpar :
      ((LatticeProb.graphNorm (![x] : LatticeProb.Site 1) : ℕ) : ZMod 2) =
        ((m : ℕ) : ZMod 2) := by
    dsimp [x]
    exact graphNorm_two_mul_sub_parity m k
  have hAB : |A - B| ≤ C / (m : ℝ) := by
    simpa [A, B, a] using hlocal m hm (![x] : LatticeProb.Site 1) hxpar
  have hDE : |D - E| ≤ C / (m : ℝ) := by
    have hEq : |D - E| = |Real.sqrt (m : ℝ) *
        LatticeProb.srwHeat 1 (2 * m) ![0] -
          Real.sqrt (m : ℝ) * 2 *
            LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0]| := by
      congr 1
      dsimp [D, E, d, e]
      ring
    rw [hEq]
    exact srwHeat_one_return_scaled_error C hC.le hlocal m hm
  have hE : E = (Real.sqrt Real.pi)⁻¹ := by
    simpa [E, e] using ctGauss_one_return_scaled m (Nat.zero_lt_of_lt hm)
  have hpiRoot : Real.sqrt Real.pi ≤ 2 := by
    calc
      Real.sqrt Real.pi ≤ Real.sqrt 4 := Real.sqrt_le_sqrt Real.pi_lt_four.le
      _ = 2 := by norm_num
  have hEhalf : 1 / 2 ≤ E := by
    rw [hE, inv_eq_one_div, div_le_div_iff₀ (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)]
    nlinarith [hpiRoot]
  have hCsmall : C / (m : ℝ) < 1 / 4 := by
    rw [div_lt_iff₀ hmReal]
    nlinarith [hmLarge1]
  have hDlow : 1 / 4 ≤ D := by
    have hlow := (abs_le.mp hDE).1
    dsimp [D]
    nlinarith [hEhalf, hCsmall]
  have hDpos : 0 < D := by linarith
  have hEpos : 0 < E := by rw [hE]; positivity
  have haBounds := srwHeat_one_scaled_bounds m hm x
  have hbBounds := ctGauss_one_scaled_bounds m hm x
  have hAlo : -2 ≤ A := by
    have : 0 ≤ A := by simpa [A, a] using haBounds.1
    linarith
  have hAhi : A ≤ 2 := by simpa [A, a] using haBounds.2
  have hBlo : -2 ≤ B := by
    have : 0 ≤ B := by simpa [B] using hbBounds.1
    linarith
  have hBhi : B ≤ 2 := by simpa [B] using hbBounds.2
  have hmass : WalkTails.hypergeometricWeight m k = a ^ 2 / d := by
    have hsite : (k : ℤ) - ((m - k : ℕ) : ℤ) = x := by
      dsimp [x]
      push_cast [Nat.cast_sub hk]
      ring
    rw [← WalkTails.hypergeometricIntWeight_eq_nat]
    rw [hypergeometricIntWeight_eq_srwHeat_sq_div_return m k hk, hsite]
  have hdpos : 0 < d := by
    have hdenEq : LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] =
        (Nat.choose (2 * m) m : ℝ) / 2 ^ (2 * m) := by
      have hden := LatticeProb.srwHeat_one_binom (2 * m) m m (by omega)
      have hsite : (m : ℤ) - (m : ℤ) = 0 := by ring
      rw [hsite] at hden
      exact hden
    have hchoose : 0 < Nat.choose (2 * m) m := Nat.choose_pos (by omega)
    dsimp [d]
    rw [hdenEq]
    exact div_pos (by exact_mod_cast hchoose) (by positivity)
  have hscaledMass : Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k =
      A ^ 2 / D := by
    rw [hmass]
    dsimp [A, D, a, d]
    field_simp [hmReal.ne', hdpos.ne', hDpos.ne']
  have hscaledGaussian : B ^ 2 / E =
      2 / Real.sqrt Real.pi *
        Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) := by
    have hprof := ctGauss_one_pair_profile m (Nat.zero_lt_of_lt hm) x
    have hsqrtmpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmReal
    have hepos : 0 < e := by
      have hprod : 0 < Real.sqrt (m : ℝ) * e := by simpa [E] using hEpos
      exact (mul_pos_iff_of_pos_left hsqrtmpos).mp hprod
    calc
      B ^ 2 / E = Real.sqrt (m : ℝ) *
          ((2 * LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x]) ^ 2 / e) := by
            dsimp [B, E, e]
            field_simp [hsqrtmpos.ne', hepos.ne']
      _ = _ := by simpa [x] using hprof
  have herr : |A ^ 2 / D - B ^ 2 / E| ≤ 48 * C / (m : ℝ) := by
    calc
      |A ^ 2 / D - B ^ 2 / E| ≤ 16 * |A - B| + 32 * |D - E| :=
        abs_sq_ratio_sub_le hDlow hEhalf hAlo hAhi hBlo hBhi
      _ ≤ 16 * (C / (m : ℝ)) + 32 * (C / (m : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hAB (by norm_num))
          (mul_le_mul_of_nonneg_left hDE (by norm_num))
      _ = 48 * C / (m : ℝ) := by ring
  calc
    |Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k -
        2 / Real.sqrt Real.pi *
          Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))| =
        |A ^ 2 / D - B ^ 2 / E| := by rw [hscaledMass, hscaledGaussian]
    _ ≤ 48 * C / (m : ℝ) := herr
end Critical2DKPZ.SHF.Moments
end
