module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
@[expose] public section
/-! # Strong L² limits for bounded scalar coefficients -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
variable {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] (μ : Measure α)
end
end GinibrePoincare
