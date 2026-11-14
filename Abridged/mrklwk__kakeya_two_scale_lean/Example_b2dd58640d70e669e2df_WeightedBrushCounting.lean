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

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Examples.Example_b2dd58640d70e669e2df_WeightedBrushCounting ====
@[expose] public section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X J : Type*} [MeasurableSpace X]
def weightedOverlap (family : Finset J) (sets : J → Set X) (w : J → ℝ) (x : X) : ℝ :=
  ∑ j ∈ family, (sets j).indicator (fun _ => w j) x


set_option linter.unusedVariables false in
/-- Each incident tube contributes at most its full-volume cap to the plane
integral. Incidence is literal nonempty intersection, not a substituted count. -/
theorem plane_integral_le_incident_weight (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (tubes : J → Set X) (w : J → ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (tubes j))
    (hw : ∀ j ∈ family, 0 ≤ w j) (H : Set X) (V : ℝ)
    (hV : ∀ j ∈ family, μ.real (tubes j) ≤ V) 
    (h_KakeyaTwoScale_integral_weightedOverlap : ∀ {X : Type u_1} {J : Type u_2} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (family : Finset J) (sets : J → Set X) (w : J → ℝ),
      (∀ j ∈ family, MeasurableSet (sets j)) →
        ∫ (x : X), KakeyaTwoScale.weightedOverlap family sets w x ∂μ =
          ∑ j ∈ family, w j * μ.real (sets j))
    :
    (∫ x in H, weightedOverlap family tubes w x ∂μ) ≤
      V * ∑ j ∈ family.filter (fun j => (tubes j ∩ H).Nonempty), w j := by
  rw [h_KakeyaTwoScale_integral_weightedOverlap (μ.restrict H) family tubes w hm]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  have he : (μ.restrict H).real (tubes j) = μ.real (tubes j ∩ H) := by
    rw [Measure.real, Measure.restrict_apply (hm j hj)]; rfl
  rw [he]
  split_ifs with hn
  · have hv : μ.real (tubes j ∩ H) ≤ V :=
      (measureReal_mono Set.inter_subset_left).trans (hV j hj)
    nlinarith [mul_le_mul_of_nonneg_left hv (hw j hj)]
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    simp

end KakeyaTwoScale
