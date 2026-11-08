/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.SHF.Moments.PairBlockCompositionVariance
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedLocalCLT
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
end Critical2DKPZ.SHF.Moments
end
