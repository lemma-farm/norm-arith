-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
abbrev Vec3 := Fin 3 → ℝ
abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)
def ParabolicPoint := Vec3 × ℝ
theorem half_pos : 0 < (1 / 2 : ℝ) := by norm_num
theorem half_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
abbrev SnowTime := Metric.Snowflaking ℝ (1 / 2 : ℝ) half_pos half_le_one
def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)
instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))
instance : MeasurableSpace SnowTime := borel SnowTime
instance : BorelSpace SnowTime := ⟨rfl⟩
def parabolicMeasurableEquiv : ParabolicPoint ≃ᵐ L2Vec3 × SnowTime :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 Vec3) {
    toEquiv := Metric.Snowflaking.toSnowflaking
    measurable_toFun := Metric.Snowflaking.continuous_toSnowflaking.measurable
    measurable_invFun := Metric.Snowflaking.homeomorph.continuous.measurable }
def parabolicMap (p : ParabolicPoint) :
    L2Vec3 × SnowTime := parabolicMeasurableEquiv p
lemma parabolicMap_injective : Function.Injective parabolicMap := by
  intro p q h
  exact parabolicMeasurableEquiv.injective h
noncomputable instance parabolicMetricSpace : MetricSpace ParabolicPoint :=
  MetricSpace.induced parabolicMap parabolicMap_injective inferInstance
abbrev parabolicPseudoMetricSpace : PseudoMetricSpace ParabolicPoint :=
  MetricSpace.toPseudoMetricSpace (self := parabolicMetricSpace)
instance : SecondCountableTopology ParabolicPoint :=
  Topology.IsInducing.secondCountableTopology (Topology.IsInducing.induced parabolicMap)
instance : BorelSpace ParabolicPoint :=
  MeasurableEmbedding.borelSpace parabolicMeasurableEquiv.measurableEmbedding
    (Topology.IsInducing.induced parabolicMap)
lemma vec3EuclideanNorm_eq_l2 (v : Vec3) :
    vec3EuclideanNorm v = ‖WithLp.toLp 2 v‖ := by
  rw [vec3EuclideanNorm, PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sq_abs]
lemma vec3EuclideanNorm_nonneg (v : Vec3) : 0 ≤ vec3EuclideanNorm v := by
  exact Real.sqrt_nonneg _
lemma vec3EuclideanNorm_smul (a : ℝ) (v : Vec3) :
    vec3EuclideanNorm (a • v) = |a| * vec3EuclideanNorm v := by
  rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    ← vec3EuclideanNorm_eq_l2]
def parabolicDist (p q : ParabolicPoint) : ℝ :=
  max (vec3EuclideanNorm (p.1 - q.1)) (Real.sqrt |p.2 - q.2|)
lemma dist_eq_parabolicDist (p q : ParabolicPoint) :
    dist p q = parabolicDist p q := by
  simp only [parabolicDist, vec3EuclideanNorm_eq_l2, Real.sqrt_eq_rpow]
  rfl
def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t
@[simp] lemma mem_vec3Ball {x y : Vec3} {r : ℝ} :
    y ∈ vec3Ball x r ↔ vec3EuclideanNorm (y - x) < r := Iff.rfl
instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))
lemma vec3Ball_measurable (x : Vec3) (r : ℝ) : MeasurableSet (vec3Ball x r) := by
  have hmeas : Measurable (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact hmeas measurableSet_Iio
lemma volume_vec3Ball (x : Vec3) (r : ℝ) :
    volume (vec3Ball x r) = volume (vec3Ball 0 r) := by
  have hpre : (fun y : Vec3 => x + y) ⁻¹' vec3Ball x r = vec3Ball 0 r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, sub_zero]
    abel_nf
  have h := (measurePreserving_add_left (volume : Measure Vec3) x).measure_preimage
    (vec3Ball_measurable x r).nullMeasurableSet
  rw [hpre] at h
  exact h.symm
lemma volume_parabolicCylinder (x : Vec3) (t r : ℝ) :
    volume (parabolicCylinder x t r) =
      volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2) := by
  rw [parabolicCylinder]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t) =
    volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2)
  rw [Measure.prod_prod]
  rw [Real.volume_Ioc]
  congr 2
  ring
lemma metricBall_subset_parabolicCylinder {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    @Metric.ball ParabolicPoint parabolicPseudoMetricSpace
      (x, t - r ^ 2 / 2) (r / 2) ⊆
      parabolicCylinder x t r := by
  rintro (p : ParabolicPoint) hp
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) < r / 2 at hp
  have hdist : @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) =
      parabolicDist p (x, t - r ^ 2 / 2) := by
    exact dist_eq_parabolicDist p (x, t - r ^ 2 / 2)
  rw [hdist] at hp
  have hp' := hp
  rcases p with ⟨y, s⟩
  rcases (max_lt_iff.mp hp') with ⟨hspace, htime⟩
  have hspace' : vec3EuclideanNorm (y - x) < r := by
    exact hspace.trans (half_lt_self hr)
  have habs : |s - (t - r ^ 2 / 2)| < (r / 2) ^ 2 :=
    (Real.sqrt_lt' (div_pos hr (by norm_num))).mp htime
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  have hrq : (r / 2) ^ 2 < r ^ 2 / 2 := by
    calc
      (r / 2) ^ 2 = (1 / 4 : ℝ) * r ^ 2 := by ring
      _ < (1 / 2 : ℝ) * r ^ 2 :=
        mul_lt_mul_of_pos_right (by norm_num) (sq_pos_of_pos hr)
      _ = r ^ 2 / 2 := by ring
  have hsum : r ^ 2 / 2 + (r / 2) ^ 2 < r ^ 2 := by
    calc
      r ^ 2 / 2 + (r / 2) ^ 2 < r ^ 2 / 2 + r ^ 2 / 2 :=
        add_lt_add_right hrq (r ^ 2 / 2)
      _ = r ^ 2 := by ring
  have hlow : t - r ^ 2 < s := by
    calc
      t - r ^ 2 < (t - r ^ 2 / 2) - (r / 2) ^ 2 := by
        calc
          t - r ^ 2 < t - (r ^ 2 / 2 + (r / 2) ^ 2) :=
            sub_lt_sub_left hsum t
          _ = (t - r ^ 2 / 2) - (r / 2) ^ 2 := by ring
      _ < s := by
        calc
          (t - r ^ 2 / 2) - (r / 2) ^ 2 <
              (t - r ^ 2 / 2) + (s - (t - r ^ 2 / 2)) :=
            by
              convert add_lt_add_left hlo (t - r ^ 2 / 2) using 1 <;> ring
          _ = s := by ring
  have hupp : s ≤ t := by
    have hslt : s < (t - r ^ 2 / 2) + (r / 2) ^ 2 := by
      exact (sub_lt_iff_lt_add.mp hhi) |>.trans_eq (add_comm _ _)
    exact le_of_lt (by
      calc
        s < (t - r ^ 2 / 2) + (r / 2) ^ 2 := hslt
        _ < t := by
          have h := add_lt_add_left hrq (t - r ^ 2 / 2)
          convert h using 1 <;> ring)
  exact ⟨hspace', hlow, hupp⟩
lemma parabolicCylinder_subset_metricBall {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    parabolicCylinder x t r ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace
        (x, t - r ^ 2 / 2) r := by
  rintro p hp
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) < r
  have hdist : @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) =
      parabolicDist p (x, t - r ^ 2 / 2) := by
    exact dist_eq_parabolicDist p (x, t - r ^ 2 / 2)
  rw [hdist]
  rcases p with ⟨y, s⟩
  rcases hp with ⟨hspace, hlow, hupp⟩
  change vec3EuclideanNorm (y - x) < r at hspace
  change t - r ^ 2 < s at hlow
  change s ≤ t at hupp
  refine max_lt hspace ?_
  apply (Real.sqrt_lt' hr).mpr
  apply abs_lt.mpr
  constructor
  · calc
      -(r ^ 2) < -r ^ 2 / 2 := by
        have h : r ^ 2 / 2 < r ^ 2 := by
          have h' : 0 < r ^ 2 / 2 := by positivity
          calc
            r ^ 2 / 2 < r ^ 2 / 2 + r ^ 2 / 2 := by
              calc
                r ^ 2 / 2 = 0 + r ^ 2 / 2 := (zero_add _).symm
                _ < r ^ 2 / 2 + r ^ 2 / 2 := add_lt_add_left h' _
            _ = r ^ 2 := by ring
        have h' := neg_lt_neg h
        calc
          -(r ^ 2) < -(r ^ 2 / 2) := h'
          _ = -r ^ 2 / 2 := by ring
      _ < s - (t - r ^ 2 / 2) := by
        have h := sub_lt_sub_right hlow (t - r ^ 2 / 2)
        calc
          -r ^ 2 / 2 = (t - r ^ 2) - (t - r ^ 2 / 2) := by ring
          _ < s - (t - r ^ 2 / 2) := h
  · calc
      s - (t - r ^ 2 / 2) ≤ r ^ 2 / 2 := by
        apply (sub_le_iff_le_add).2
        calc
          s ≤ t := hupp
          _ = r ^ 2 / 2 + (t - r ^ 2 / 2) := by ring
      _ < r ^ 2 := by
        have h : 0 < r ^ 2 / 2 := by positivity
        calc
          r ^ 2 / 2 < r ^ 2 / 2 + r ^ 2 / 2 := by
            calc
              r ^ 2 / 2 = 0 + r ^ 2 / 2 := (zero_add _).symm
              _ < r ^ 2 / 2 + r ^ 2 / 2 := add_lt_add_left h _
          _ = r ^ 2 := by ring
end CKN.Foundation.Parabolic
