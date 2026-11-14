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

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Examples.Example_6ed8fda8c552d1eba17e_WeightedBrushCounting ====
@[expose] public section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X J : Type*} [MeasurableSpace X]


/-- High overlap on a measurable union forces an integral on every containing
plane neighborhood. F is nonnegative on that neighborhood. -/
theorem high_overlap_plane_integral (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → ℝ) (hF : Integrable F μ) (hn : ∀ x, 0 ≤ F x)
    (U H : Set X) (hU : MeasurableSet U) (hH : MeasurableSet H)
    (hsub : U ⊆ H) (M : ℝ) (hM : ∀ x ∈ U, M ≤ F x) :
    M * μ.real U ≤ ∫ x in H, F x ∂μ := by
  have hi : Integrable (U.indicator (fun _ => M)) μ := (integrable_const M).indicator hU
  calc
    _ = ∫ x, U.indicator (fun _ => M) x ∂μ := by
      rw [integral_indicator_const M hU]; simp [smul_eq_mul, mul_comm]
    _ ≤ ∫ x, H.indicator F x ∂μ := by
      apply integral_mono hi (hF.indicator hH)
      intro x
      by_cases hx : x ∈ U
      · simpa [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)] using hM x hx
      · by_cases hh : x ∈ H
        · simpa [Set.indicator_of_notMem hx, Set.indicator_of_mem hh] using hn x
        · simp [hx, hh]
    _ = _ := integral_indicator hH

end KakeyaTwoScale
