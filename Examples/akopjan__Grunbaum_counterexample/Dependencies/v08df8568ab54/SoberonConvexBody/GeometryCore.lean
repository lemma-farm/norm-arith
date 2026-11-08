import Mathlib
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.Walsh4
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.Cells
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.Tensors
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.FrameGeometry
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Geometric and measure-theoretic reduction

Unlike the earlier draft, this file does not package the analytic content in a
single certificate.  Every remaining analytic statement is exposed as a named
lemma with concrete definitions.
-/
noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev HyperplaneCfg := Cells.HyperplaneCfg
def walsh (μ : Measure E4) (c : HyperplaneCfg) (I : Walsh4.Index) : ℝ :=
  ∫ x, Cells.signCharacter c I x ∂μ
theorem norm_coe_unitSphere
    (u : Metric.sphere (0 : E4) 1) : ‖(u : E4)‖ = 1 := by
  exact SphereGeometry.norm_coe u
private noncomputable def fourthRoot (a : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt a)
private theorem fourthRoot_pos {a : ℝ} (ha : 0 < a) : 0 < fourthRoot a := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 ha)
private theorem fourthRoot_pow_four {a : ℝ} (ha : 0 ≤ a) :
    fourthRoot a ^ 4 = a := by
  calc
    fourthRoot a ^ 4 = (Real.sqrt (Real.sqrt a) ^ 2) ^ 2 := by
      simp only [fourthRoot]
      ring
    _ = (Real.sqrt a) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg a)]
    _ = a := Real.sq_sqrt ha
/-- In dimension four, the radial Haar factor assigns mass `a / 4` to the
positive radii whose fourth power is at most `a`. -/
theorem volumeIoiPow_three_radialSlice
    (a : ℝ) (ha : 0 ≤ a) :
    Measure.volumeIoiPow 3
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ a} =
      ENNReal.ofReal (a / 4) := by
  by_cases ha0 : a = 0
  · subst a
    have hempty :
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ (0 : ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro r hr
      have hle : (r : ℝ) ^ 4 ≤ 0 := hr
      exact (not_le_of_gt (pow_pos r.property 4)) hle
    simp [hempty]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let rho : ℝ := fourthRoot a
    have hrho : 0 < rho := fourthRoot_pos ha'
    let r0 : Set.Ioi (0 : ℝ) := ⟨rho, hrho⟩
    have hrho4 : rho ^ 4 = a := fourthRoot_pow_four ha
    have hslice :
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ a} = Set.Iic r0 := by
      ext r
      change (r : ℝ) ^ 4 ≤ a ↔ r ≤ r0
      rw [← Subtype.coe_le_coe]
      have hr0 : 0 ≤ (r : ℝ) := le_of_lt r.property
      have hrho0 : 0 ≤ rho := le_of_lt hrho
      have hp :=
        pow_le_pow_iff_left₀ hr0 hrho0 (by norm_num : (4 : ℕ) ≠ 0)
      simpa [r0, hrho4] using hp
    rw [hslice]
    have hdisj : Disjoint (Set.Iio r0) ({r0} : Set (Set.Ioi (0 : ℝ))) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hxr
      have hxlt : x < r0 := hx
      have hxeq : x = r0 := Set.mem_singleton_iff.mp hxr
      exact (ne_of_lt hxlt) hxeq
    have hsingle :
        Measure.volumeIoiPow 3 ({r0} : Set (Set.Ioi (0 : ℝ))) = 0 := by
      rw [Measure.volumeIoiPow,
        withDensity_apply _ (measurableSet_singleton r0)]
      have hbase :
          (Measure.comap Subtype.val volume)
              ({r0} : Set (Set.Ioi (0 : ℝ))) = 0 := by
        rw [comap_subtype_coe_apply measurableSet_Ioi]
        simp
      exact setLIntegral_measure_zero _ _ hbase
    calc
      Measure.volumeIoiPow 3 (Set.Iic r0)
          = Measure.volumeIoiPow 3 (Set.Iio r0 ∪ {r0}) := by
              rw [Set.Iio_union_right]
      _ = Measure.volumeIoiPow 3 (Set.Iio r0) +
            Measure.volumeIoiPow 3 ({r0} : Set (Set.Ioi (0 : ℝ))) := by
              exact measure_union hdisj (measurableSet_singleton r0)
      _ = Measure.volumeIoiPow 3 (Set.Iio r0) := by rw [hsingle, add_zero]
      _ = ENNReal.ofReal ((r0 : ℝ) ^ 4 / 4) := by
            have hpow := Measure.volumeIoiPow_apply_Iio 3 r0
            norm_num at hpow
            exact hpow
      _ = ENNReal.ofReal (a / 4) := by
            simp only [r0]
            rw [hrho4]
/-- Projecting a four-dimensional radial region in polar coordinates onto its
angular variable produces the expected density `a(u) / 4` on the sphere. -/
theorem map_fst_restrict_radialProduct
    (a : Metric.sphere (0 : E4) 1 → ℝ)
    (ha : Measurable a) (hpos : ∀ u, 0 ≤ a u) :
    Measure.map Prod.fst
        ((volume.toSphere.prod (Measure.volumeIoiPow 3)).restrict
          {p : Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ) |
            (p.2 : ℝ) ^ 4 ≤ a p.1}) =
      volume.toSphere.withDensity
        (fun u => (Real.toNNReal (a u / 4) : ENNReal)) := by
  let S : Set (Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) ^ 4 ≤ a p.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply measurable_fst hT]
  rw [Measure.restrict_apply (measurable_fst hT)]
  rw [Measure.prod_apply ((measurable_fst hT).inter hS)]
  rw [withDensity_apply _ hT]
  rw [← lintegral_indicator hT]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ T
  · have hpre :
        Prod.mk u ⁻¹' (Prod.fst ⁻¹' T ∩ S) =
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ a u} := by
      ext r
      simp [S, hu]
    rw [hpre, volumeIoiPow_three_radialSlice (a u) (hpos u)]
    simp [hu, ENNReal.ofReal]
  · have hpre : Prod.mk u ⁻¹' (Prod.fst ⁻¹' T ∩ S) = ∅ := by
      ext r
      simp [S, hu]
    rw [hpre]
    simp [hu]
end SoberonConvexBody
