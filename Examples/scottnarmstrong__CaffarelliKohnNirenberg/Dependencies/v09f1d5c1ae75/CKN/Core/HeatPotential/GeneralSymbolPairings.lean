-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.Step3.LocalizedEquationDuhamel
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
private lemma parabolic_sub_measurePreserving (y : ParabolicPoint) :
    MeasurePreserving (fun x : ParabolicPoint => pointSub x y)
      (volume : Measure ParabolicPoint) volume := by
  have h := (measurePreserving_add_right (volume : Measure Vec3) (-y.1)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-y.2))
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving (fun x : Vec3 × ℝ =>
    (x.1 + -y.1, x.2 + -y.2)) (volume.prod volume) (volume.prod volume)
  convert h using 1
  rfl
private lemma parabolic_integrableOn_shift_complex
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    {K : Set ParabolicPoint} (hK : IsCompact K) (y : ParabolicPoint) :
    IntegrableOn (fun x : ParabolicPoint => k (pointSub x y)) K volume := by
  let S : Set ParabolicPoint := (fun x : ParabolicPoint => pointSub x y) '' K
  have hS : IsCompact S := by
    apply hK.image
    change Continuous (fun x : ParabolicPoint =>
      parabolicHomeomorph.symm (x.1 - y.1, x.2 - y.2))
    apply parabolicHomeomorph.continuous_symm.comp
    exact ((continuous_fst_parabolicPoint.sub continuous_const).prodMk
      (continuous_snd_parabolicPoint.sub continuous_const))
  have hkS : IntegrableOn k S volume := hk.integrableOn_isCompact hS
  have hInd := hkS.integrable_indicator hS.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hInd.aestronglyMeasurable |>.mpr hInd
  have heq : (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) =
      (fun x : ParabolicPoint => K.indicator
        (fun z : ParabolicPoint => k (pointSub z y)) x) := by
    funext x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ S := ⟨x, hx, rfl⟩
      simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hx]
    · have hxy : pointSub x y ∉ S := by
        rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := by
          apply Prod.ext
          · exact sub_left_injective (b := y.1)
              (by simpa [pointSub] using congrArg Prod.fst hzx)
          · exact sub_left_injective (b := y.2)
              (by simpa [pointSub] using congrArg Prod.snd hzx)
        exact hx (by simpa only [hzx'] using hz)
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy]
  have hcomp' : Integrable (fun x : ParabolicPoint =>
      K.indicator (fun z : ParabolicPoint => k (pointSub z y)) x) volume := by
    rw [← heq]
    change Integrable (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) volume at hcomp
    exact hcomp
  exact (integrable_indicator_iff hK.measurableSet).mp hcomp'
private lemma parabolic_setIntegral_norm_shift_le_complex
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    {K L : Set ParabolicPoint} (hK : IsCompact K) (hL : IsCompact L)
    (y : ParabolicPoint)
    (hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L) :
    (∫ x in K, ‖k (pointSub x y)‖) ≤ ∫ z in L, ‖k z‖ := by
  have hkn : LocallyIntegrable (fun z : ParabolicPoint => ‖k z‖) volume := by
    intro x
    rcases hk x with ⟨U, hU, hInt⟩
    exact ⟨U, hU, hInt.norm⟩
  have hshift : IntegrableOn (fun x : ParabolicPoint =>
      ‖k (pointSub x y)‖) K volume := by
    exact (parabolic_integrableOn_shift_complex hk hK y).integrable.norm
  have hleft := hshift.integrable_indicator hK.measurableSet
  have hright0 := hkn.integrableOn_isCompact hL
  have hright := hright0.integrable_indicator hL.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hright.aestronglyMeasurable |>.mpr hright
  have hle : ∀ᵐ x : ParabolicPoint, K.indicator
      (fun z : ParabolicPoint => ‖k (pointSub z y)‖) x ≤
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ L := hsub ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
    · rw [Set.indicator_of_notMem hx]
      by_cases hLxy : pointSub x y ∈ L
      · rw [Set.indicator_of_mem hLxy]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem hLxy]
  have hint := integral_mono_ae hleft hcomp hle
  rw [integral_indicator hK.measurableSet] at hint
  let e := (Homeomorph.subRight y.1).prodCongr (Homeomorph.subRight y.2)
  have htrans := (parabolic_sub_measurePreserving y).integral_comp
    e.measurableEmbedding (L.indicator (fun z : ParabolicPoint => ‖k z‖))
  have htrans' : (∫ x : ParabolicPoint,
      (L.indicator (fun z : ParabolicPoint => ‖k z‖) ∘
        fun x : ParabolicPoint => pointSub x y) x) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z := by
    change (∫ x : ParabolicPoint,
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z at htrans
    exact htrans
  rw [htrans', integral_indicator hL.measurableSet] at hint
  exact hint
end CKN.Core.HeatPotential
