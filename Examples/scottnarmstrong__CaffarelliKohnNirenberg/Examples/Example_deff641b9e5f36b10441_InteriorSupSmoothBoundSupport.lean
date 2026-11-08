-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.InteriorEstimates
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Parabolic.BallBasics
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.InteriorSupThreeQuarters
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
lemma cutoff_annulus_norm_distance_for_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) :
    ρ / 30 < ‖x - y‖ := by
  have hx' : vec3EuclideanNorm (x - x₀) < 3 * ρ / 4 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy' : 13 * (4 * ρ / 3) / 20 < vec3EuclideanNorm (y - x₀) := by
    have hnot : y ∉ euclideanClosedBall x₀ (13 * (4 * ρ / 3) / 20) := hy.2
    by_contra hle
    apply hnot
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact le_of_not_gt (by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        using hle)
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (x - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x₀)‖ =
          ‖WithLp.toLp 2 ((y - x) + (x - x₀))‖ := by
            congr 1
            ext i
            simp
      _ ≤ ‖WithLp.toLp 2 (y - x)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := norm_add_le _ _
      _ = _ := by
        rw [show y - x = -(x - y) by ext i; simp,
          WithLp.toLp_neg, norm_neg]
  have hEuclideanGap : 7 * ρ / 60 < vec3EuclideanNorm (x - y) := by
    rw [show 13 * (4 * ρ / 3) / 20 = 13 * ρ / 15 by ring] at hy'
    nlinarith only [hx', hy', htri]
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
  have hthree' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  nlinarith only [hEuclideanGap, hthree', hρ]
/-- Bounds the differentiated cutoff kernel at the three-quarter scale. -/
lemma kernel_cutoff_derivative_bound_scaled_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) (i j : Fin 3) :
    |CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) j y| ≤
      harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
  have hdist := cutoff_annulus_norm_distance_for_three_quarters hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  rw [spatialDeriv_kernelCutoffDerivative_of_ne (by positivity) hxy]
  calc
    |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y *
          CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) j y| ≤
        |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| *
          |CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y| +
        |newtonianKernel (x - y)| *
          |CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) j y| := by
      calc
        |_ + _| ≤ |_| + |_| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ *
          (cutoffGradientConstant / (4 * ρ / 3)) +
        (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ *
          (cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
      have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
      have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 30) ^ 2)⁻¹ := by gcongr
      have heta := eta_spatialDeriv_bound_global x₀
        (ρ := 4 * ρ / 3) (by positivity) y i
      have hsecond := eta_spatialSecond_bound_global x₀
        (ρ := 4 * ρ / 3) (by positivity) y i j
      have hkernel := newtonianKernel_size_bound hxy
      have hdistinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
      have hderiv' : |CKN.spatialDeriv newtonianKernel j (x - y)| ≤
          (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ :=
        hderiv.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
      have hkernel' : |newtonianKernel (x - y)| ≤
          (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ :=
        hkernel.trans (mul_le_mul_of_nonneg_left hdistinv (by positivity))
      rw [show |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| =
          |CKN.spatialDeriv newtonianKernel j (x - y)| by
            rw [spatialDeriv_newtonianKernel_shift_eq_neg hxy, abs_neg]]
      gcongr
    _ = harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
      dsimp [harmonicInteriorGradientConstant]
      field_simp [hρ.ne']
      ring
end CKN.Foundation.Heat
