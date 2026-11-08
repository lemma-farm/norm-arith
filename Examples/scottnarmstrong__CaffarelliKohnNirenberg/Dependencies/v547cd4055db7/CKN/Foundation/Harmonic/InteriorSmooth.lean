-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Harmonic.InteriorRegularity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
private lemma fderiv_norm_le_three_classicalGradient_smooth
    {f : Vec3 → ℝ} (x : Vec3) :
    ‖fderiv ℝ f x‖ ≤ 3 * vec3EuclideanNorm (classicalGradient f x) := by
  have hbase : ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    calc
      ‖(fderiv ℝ f x) z‖ =
          ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
        calc
          ‖(fderiv ℝ f x) z‖ =
              ‖(fderiv ℝ f x) (∑ i : Fin 3, z i • basisVec i)‖ := by
                rw [sum_smul_basisVec]
          _ = ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
            rw [_root_.map_sum]
            simp only [map_smul]
      _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        have hz : |z i| ≤ ‖z‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
        have hg : |(fderiv ℝ f x) (basisVec i)| ≤
            ‖classicalGradient f x‖ := by
          simpa only [classicalGradient_apply, Real.norm_eq_abs] using
            norm_le_pi_norm (classicalGradient f x) i
        exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
      _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (CKN.space_norm_le_euclideanNorm (classicalGradient f x)) (by positivity))
end CKN.Foundation.Heat
