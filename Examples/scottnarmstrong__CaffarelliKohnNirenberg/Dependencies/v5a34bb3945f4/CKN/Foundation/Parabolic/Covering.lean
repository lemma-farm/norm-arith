-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Doubling
import Mathlib.MeasureTheory.Covering.Vitali
set_option autoImplicit false
set_option warningAsError true
/-!
# A parabolic Vitali covering estimate

This file records the measure estimate obtained by applying the Vitali
covering theorem to the metric balls associated with the parabolic cylinders.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
private abbrev parabolicMetricBall (c : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c r
private lemma volume_vec3Ball_finite (x : Vec3) :
    volume (vec3Ball x 2) < (∞ : ℝ≥0∞) := by
  have hsub : vec3Ball x 2 ⊆ @Metric.ball Vec3 inferInstance x 2 := by
    intro y hy
    change vec3EuclideanNorm (y - x) < 2 at hy
    rw [Metric.mem_ball]
    change ‖y - x‖ < 2
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun b => ‖(y - x) b‖₊) < (2 : ℝ≥0) := by
      apply (Finset.sup_lt_iff (by norm_num)).2
      intro i hi
      have hi' : ‖(WithLp.toLp 2 (y - x)).ofLp i‖ ≤
          ‖WithLp.toLp 2 (y - x)‖ := PiLp.norm_apply_le _ i
      have hi'' : ‖y i - x i‖ ≤ vec3EuclideanNorm (y - x) := by
        rw [vec3EuclideanNorm_eq_l2]
        exact hi'
      have hreal : ‖y i - x i‖ < (2 : ℝ) := lt_of_le_of_lt hi'' hy
      exact_mod_cast hreal
    exact_mod_cast hsup
  exact (measure_mono hsub).trans_lt measure_ball_lt_top
private lemma parabolicMetricBall_subset_finiteCylinder (p : ParabolicPoint) :
    parabolicMetricBall p 1 ⊆
      parabolicCylinder p.1 (p.2 + 1) 2 := by
  rcases p with ⟨x, t⟩
  rintro q hs
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      q ((x, t) : ParabolicPoint) < 1 at hs
  rw [dist_eq_parabolicDist q ((x, t) : ParabolicPoint)] at hs
  rcases q with ⟨y, s⟩
  rcases max_lt_iff.mp hs with ⟨hspace, htime⟩
  have habs : |s - t| < 1 := by
    simpa using (Real.sqrt_lt' one_pos).mp htime
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  change (y, s) ∈ parabolicCylinder x (t + 1) 2
  exact ⟨hspace.trans (by norm_num), by linarith only [hlo], le_of_lt (by
    linarith only [hhi])⟩
private lemma volume_parabolicMetricBall_finite (p : ParabolicPoint) :
    volume (parabolicMetricBall p 1) < (∞ : ℝ≥0∞) := by
  have hfinite : volume (parabolicCylinder p.1 (p.2 + 1) 2) < (∞ : ℝ≥0∞) := by
    rw [volume_parabolicCylinder]
    exact ENNReal.mul_lt_top (volume_vec3Ball_finite p.1) (by norm_num)
  exact (measure_mono (parabolicMetricBall_subset_finiteCylinder p)).trans_lt hfinite
private instance parabolicVolumeIsLocallyFinite :
    IsLocallyFiniteMeasure (volume : Measure ParabolicPoint) :=
  { finiteAtNhds := fun p =>
      ⟨parabolicMetricBall p 1,
        @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p 1 one_pos,
        volume_parabolicMetricBall_finite p⟩ }
end CKN.Foundation.Parabolic
