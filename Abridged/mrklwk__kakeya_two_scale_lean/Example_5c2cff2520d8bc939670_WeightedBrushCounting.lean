module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Dependencies.vf240e0e86015.KakeyaTwoScale.SegmentGeometry ====
public section
@[expose] public section
open Metric
namespace KakeyaTwoScale
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def segmentPoint (b v : E) (t : ℝ) : E := b+t • v

end KakeyaTwoScale

end
end

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Examples.Example_5c2cff2520d8bc939670_WeightedBrushCounting ====
@[expose] public section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X J : Type*} [MeasurableSpace X]


set_option linter.unusedVariables false in
/-- Uniform two-height localization yields a weighted overlap bound from a
precisely stated slope-neighborhood weight cap. The cap is still geometric input. -/
theorem weighted_two_height_overlap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (family : Finset J) (b v : J → Y) (w : J → ℝ)
    (s t r h B : ℝ) (p x : Y) (hh : 0 < h) (hsep : h ≤ |t-s|)
    (hw : ∀ j ∈ family, 0 ≤ w j)
    (hs : ∀ j ∈ family, dist (segmentPoint (b j) (v j) s) p ≤ r)
    (hcap : ∀ v₀ : Y, (∑ j ∈ family.filter (fun j => dist (v j) v₀ ≤ 4*r/h), w j) ≤ B)
    (hB : 0 ≤ B) 
    (h_KakeyaTwoScale_slope_dist_of_two_encounters : ∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b v b' v' : E)
      (s t r h : ℝ),
      0 < h →
        h ≤ |t - s| →
          Dist.dist (KakeyaTwoScale.segmentPoint b v s) (KakeyaTwoScale.segmentPoint b' v' s) ≤ r →
            Dist.dist (KakeyaTwoScale.segmentPoint b v t) (KakeyaTwoScale.segmentPoint b' v' t) ≤ r →
              Dist.dist v v' ≤ 2 * r / h)
    :
    (∑ j ∈ family.filter (fun j => dist (segmentPoint (b j) (v j) t) x ≤ r), w j) ≤ B := by
  let S := family.filter (fun j => dist (segmentPoint (b j) (v j) t) x ≤ r)
  by_cases hne : S.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hne
    have hj₀' := Finset.mem_filter.mp hj₀
    have hsub : S ⊆ family.filter (fun j => dist (v j) (v j₀) ≤ 4*r/h) := by
      intro j hj
      obtain ⟨hj,hjt⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hj,?_⟩
      have hdist (z z' c : Y) (hz : dist z c ≤ r) (hz' : dist z' c ≤ r) : dist z z' ≤ 2*r := by
        have hh := dist_triangle z c z'
        rw [dist_comm c z'] at hh
        linarith
      have hloc := h_KakeyaTwoScale_slope_dist_of_two_encounters (b j) (v j) (b j₀) (v j₀)
        s t (2*r) h hh hsep (hdist _ _ p (hs j hj) (hs j₀ hj₀'.1))
        (hdist _ _ x hjt hj₀'.2)
      convert hloc using 1; ring
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj _ => hw j (Finset.mem_filter.mp hj).1)).trans (hcap (v j₀))
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ j ∈ S, w j) ≤ B
    simpa [he] using hB
end KakeyaTwoScale
