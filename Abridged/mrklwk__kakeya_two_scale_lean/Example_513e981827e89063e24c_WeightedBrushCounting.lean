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

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Examples.Example_513e981827e89063e24c_WeightedBrushCounting ====
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
/-- Bounded weighted multiplicity converts counted volume to union volume. -/
theorem weighted_union_volume (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (sets : J → Set X) (w : J → ℝ) (B : ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (sets j))
    (hB : ∀ x, weightedOverlap family sets w x ≤ B) 
    (h_KakeyaTwoScale_integrable_weightedOverlap : ∀ {X : Type u_1} {J : Type u_2} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (family : Finset J) (sets : J → Set X) (w : J → ℝ),
      (∀ j ∈ family, MeasurableSet (sets j)) →
        MeasureTheory.Integrable (KakeyaTwoScale.weightedOverlap family sets w) μ)
    (h_KakeyaTwoScale_integral_weightedOverlap : ∀ {X : Type u_1} {J : Type u_2} [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X)
      [MeasureTheory.IsFiniteMeasure μ] (family : Finset J) (sets : J → Set X) (w : J → ℝ),
      (∀ j ∈ family, MeasurableSet (sets j)) →
        ∫ (x : X), KakeyaTwoScale.weightedOverlap family sets w x ∂μ =
          ∑ j ∈ family, w j * μ.real (sets j))
    :
    (∑ j ∈ family, w j * μ.real (sets j)) ≤ B * μ.real (⋃ j ∈ family, sets j) := by
  have hU : MeasurableSet (⋃ j ∈ family, sets j) := Finset.measurableSet_biUnion _ hm
  rw [← h_KakeyaTwoScale_integral_weightedOverlap μ family sets w hm]
  calc
    _ ≤ ∫ x, (⋃ j ∈ family, sets j).indicator (fun _ => B) x ∂μ := by
      apply integral_mono (h_KakeyaTwoScale_integrable_weightedOverlap μ family sets w hm)
        ((integrable_const B).indicator hU)
      intro x
      by_cases hx : x ∈ ⋃ j ∈ family, sets j
      · simpa [Set.indicator_of_mem hx] using hB x
      · have hn : ∀ j ∈ family, x ∉ sets j := by simpa using hx
        rw [Set.indicator_of_notMem hx]
        have hz : weightedOverlap family sets w x = 0 :=
          Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hn j hj) _
        rw [hz]
    _ = _ := by rw [integral_indicator_const B hU]; simp [smul_eq_mul, mul_comm]

end KakeyaTwoScale
