module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.Gauge
public import Mathlib
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
set_option autoImplicit false
/-!
# The geometric objects of Theorem 1.1

`Plane` carries the Euclidean norm. `gaugeMeasure` is Mathlib's arbitrary-gauge
Hausdorff measure, and `distanceSet` is the ordinary unpinned distance set.
-/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FalconerThetaGauge
noncomputable section
/-- The real Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- Hausdorff measure with the stretched logarithmic gauge of the manuscript. -/
def gaugeMeasure (θ : ℝ) : Measure Plane := Measure.mkMetric (thetaGauge θ)
theorem gaugeMeasure_le_hausdorffMeasure_one (θ : ℝ) :
    gaugeMeasure θ ≤ Measure.hausdorffMeasure 1 := by
  simpa [gaugeMeasure, Measure.hausdorffMeasure] using
    (Measure.mkMetric_mono (X := Plane) (Filter.Eventually.of_forall (thetaGauge_le θ)))
@[simp]
theorem gaugeMeasure_singleton (θ : ℝ) (x : Plane) : gaugeMeasure θ {x} = 0 := by
  have := Measure.nullSingletonClass_hausdorff Plane (by norm_num : (0 : ℝ) < 1)
  exact le_antisymm ((gaugeMeasure_le_hausdorffMeasure_one θ {x}).trans (by simp)) bot_le
instance nullSingletonClass_gaugeMeasure (θ : ℝ) : NullSingletonClass (gaugeMeasure θ) :=
  ⟨gaugeMeasure_singleton θ⟩
end
end FalconerThetaGauge
