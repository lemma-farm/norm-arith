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

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Examples.Example_8b2adc1ff0205beadfe7_WeightedBrushCounting ====
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
/-- The brush's plane-incidence inequality, including every multiplicity and
volume constant. Geometric localization must supply hB and the pieces. -/
theorem brush_plane_incidence (μ : Measure X) [IsFiniteMeasure μ]
    (family brush : Finset J) (tubes pieces : J → Set X) (w : J → ℝ)
    (H : Set X) (hH : MeasurableSet H) (v B M V : ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (tubes j))
    (hpm : ∀ j ∈ brush, MeasurableSet (pieces j))
    (hw : ∀ j ∈ family, 0 ≤ w j) (hpw : ∀ j ∈ brush, 0 ≤ w j)
    (hv : ∀ j ∈ brush, v ≤ μ.real (pieces j))
    (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hB : ∀ x, weightedOverlap brush pieces w x ≤ B)
    (hsub : ∀ j ∈ brush, pieces j ⊆ H)
    (hhigh : ∀ j ∈ brush, ∀ x ∈ pieces j, M ≤ weightedOverlap family tubes w x)
    (hV : ∀ j ∈ family, μ.real (tubes j) ≤ V) 
    (h_KakeyaTwoScale_high_overlap_plane_integral : ∀ {X : Type u_1} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (F : X → ℝ),
      MeasureTheory.Integrable F μ →
        (∀ (x : X), 0 ≤ F x) →
          ∀ (U H : Set X),
            MeasurableSet U →
              MeasurableSet H →
                U ⊆ H → ∀ (M : ℝ), (∀ x ∈ U, M ≤ F x) → M * μ.real U ≤ ∫ (x : X) in H, F x ∂μ)
    (h_KakeyaTwoScale_brush_counted_volume_lower : ∀ {X : Type u_1} {J : Type u_2} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (family : Finset J) (pieces : J → Set X) (w : J → ℝ) (v B : ℝ),
      (∀ j ∈ family, MeasurableSet (pieces j)) →
        (∀ j ∈ family, 0 ≤ w j) →
          (∀ j ∈ family, v ≤ μ.real (pieces j)) →
            (∀ (x : X), KakeyaTwoScale.weightedOverlap family pieces w x ≤ B) →
              v * ∑ j ∈ family, w j ≤ B * μ.real (⋃ j ∈ family, pieces j))
    (h_KakeyaTwoScale_weightedOverlap_nonneg : ∀ {X : Type u_1} {J : Type u_2} (family : Finset J) (sets : J → Set X) (w : J → ℝ),
      (∀ j ∈ family, 0 ≤ w j) → ∀ (x : X), 0 ≤ KakeyaTwoScale.weightedOverlap family sets w x)
    (h_KakeyaTwoScale_plane_integral_le_incident_weight : ∀ {X : Type u_1} {J : Type u_2} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (family : Finset J) (tubes : J → Set X) (w : J → ℝ),
      (∀ j ∈ family, MeasurableSet (tubes j)) →
        (∀ j ∈ family, 0 ≤ w j) →
          ∀ (H : Set X) (V : ℝ),
            (∀ j ∈ family, μ.real (tubes j) ≤ V) →
              ∫ (x : X) in H, KakeyaTwoScale.weightedOverlap family tubes w x ∂μ ≤
                V * ∑ j ∈ family with (tubes j ∩ H).Nonempty, w j)
    (h_KakeyaTwoScale_integrable_weightedOverlap : ∀ {X : Type u_1} {J : Type u_2} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (family : Finset J) (sets : J → Set X) (w : J → ℝ),
      (∀ j ∈ family, MeasurableSet (sets j)) →
        MeasureTheory.Integrable (KakeyaTwoScale.weightedOverlap family sets w) μ)
    :
    M*v*(∑ j ∈ brush, w j) ≤
      B*V*(∑ j ∈ family.filter (fun j => (tubes j ∩ H).Nonempty), w j) := by
  let U := ⋃ j ∈ brush, pieces j
  have hU : MeasurableSet U := Finset.measurableSet_biUnion _ hpm
  have hUH : U ⊆ H := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact hsub j hj hx
  have hHU : ∀ x ∈ U, M ≤ weightedOverlap family tubes w x := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact hhigh j hj x hx
  have harea := h_KakeyaTwoScale_brush_counted_volume_lower μ brush pieces w v B hpm hpw hv hB
  have hi := h_KakeyaTwoScale_high_overlap_plane_integral μ (weightedOverlap family tubes w)
    (h_KakeyaTwoScale_integrable_weightedOverlap μ family tubes w hm) (h_KakeyaTwoScale_weightedOverlap_nonneg family tubes w hw)
    U H hU hH hUH M hHU
  have hu := h_KakeyaTwoScale_plane_integral_le_incident_weight μ family tubes w hm hw H V hV
  calc
    _ = M*(v*∑ j ∈ brush, w j) := by ring
    _ ≤ M*(B*μ.real U) := mul_le_mul_of_nonneg_left harea hM0
    _ = B*(M*μ.real U) := by ring
    _ ≤ B*(∫ x in H, weightedOverlap family tubes w x ∂μ) :=
      mul_le_mul_of_nonneg_left hi hB0
    _ ≤ B*(V*∑ j ∈ family.filter (fun j => (tubes j ∩ H).Nonempty), w j) :=
      mul_le_mul_of_nonneg_left hu hB0
    _ = _ := by ring

end KakeyaTwoScale
