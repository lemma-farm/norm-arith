module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.OrthogonalProjectionFourier
public import Mathlib
public import Mathlib.Probability.Kernel.Composition.Lemmas
set_option autoImplicit false
/-!
# A jointly Borel family of actual orthogonal projection densities

The Radon–Nikodym kernel construction adapts
`FalconerPacking/ProjectionDensity.lean` (Yongxi Lin, Apache 2.0). Here the
parameter space is the actual Euclidean unit circle, and the hypothesis is
finite logarithmic Fourier energy, rather than a supercritical Frostman exponent.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
namespace FalconerThetaGauge
section KernelDensity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
end KernelDensity
/-- Actual inner-product projection as a measurable kernel on the Euclidean circle. -/
def orthogonalProjectionKernel (μ : Measure Plane) [SFinite μ] : Kernel UnitCircle ℝ where
  toFun w := orthogonalProjectionMeasure μ (w : Plane)
  measurable' := by
    have hm : Measurable (fun p : UnitCircle × Plane ↦ orthogonalProjection p.1 p.2) := by
      unfold orthogonalProjection
      fun_prop
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [orthogonalProjectionMeasure,
      Measure.map_apply (continuous_orthogonalProjection _).measurable hS]
    exact measurable_measure_prodMk_left (ν := μ) (hm hS)
@[simp]
theorem orthogonalProjectionKernel_apply (μ : Measure Plane) [SFinite μ] (w : UnitCircle) :
    orthogonalProjectionKernel μ w = orthogonalProjectionMeasure μ (w : Plane) := rfl
instance (μ : Measure Plane) [IsFiniteMeasure μ] : IsFiniteKernel (orthogonalProjectionKernel μ) := by
  refine ⟨μ univ, measure_lt_top _ _, fun w ↦ ?_⟩
  simp [orthogonalProjectionMeasure, Measure.map_apply (continuous_orthogonalProjection _).measurable]
instance (μ : Measure Plane) [IsProbabilityMeasure μ] : IsMarkovKernel (orthogonalProjectionKernel μ) where
  isProbabilityMeasure w := by
    rw [orthogonalProjectionKernel_apply]
    infer_instance
end FalconerThetaGauge
