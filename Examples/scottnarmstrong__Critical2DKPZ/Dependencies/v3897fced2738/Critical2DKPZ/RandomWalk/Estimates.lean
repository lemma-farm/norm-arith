/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.KernelBridge
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.GaussianBridge
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.PairedLocalCLT
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.SRWGaussBound
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Local central limit theorem and Gaussian upper bound for the simple walk kernel -/
public section
namespace Critical2DKPZ
theorem srwKernel_gaussianBound :
    ∃ C c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site,
      srwKernel n z ≤ C / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) := by
  refine ⟨9 * LatticeProb.greenConst 2, 1 / 40, by norm_num, fun n hn z => ?_⟩
  have h := LatticeProb.srwHeat_gaussian (d := 2) (by decide) hn z
  rw [← srwKernel_eq_srwHeat] at h
  norm_num [Real.rpow_neg_one] at h
  have ht : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he := gaussian_exponent_le ht (sq_nonneg ‖siteToPlane z‖)
    (norm_siteToPlane_sq_le_graphNorm_sq z)
  calc srwKernel n z
      ≤ 9 * LatticeProb.greenConst 2 * (n : ℝ)⁻¹ *
          Real.exp (-(LatticeProb.graphNorm z : ℝ) ^ 2 / (8 * ((n : ℝ) + 4))) := h
    _ ≤ 9 * LatticeProb.greenConst 2 * (n : ℝ)⁻¹ *
          Real.exp (-(1 / 40 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (mul_nonneg (mul_nonneg (by norm_num) (LatticeProb.greenConst_nonneg 2))
          (inv_nonneg.mpr (Nat.cast_nonneg n)))
    _ = _ := by simp only [div_eq_mul_inv]
end Critical2DKPZ
