-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Harmonic.InteriorEstimates
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Parabolic.BallBasics
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Harmonic.InteriorSupThreeQuarters
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
/-- Bounds the cutoff annulus away from the three-quarter ball. -/
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
end CKN.Foundation.Heat
