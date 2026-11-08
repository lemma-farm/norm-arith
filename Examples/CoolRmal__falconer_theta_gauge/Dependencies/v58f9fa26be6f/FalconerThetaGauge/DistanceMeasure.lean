module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.Statement
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
/-!
# The positive-length conclusion from a distance measure

The actual pushforward of two planar probabilities by Euclidean distance has
mass one on the all-pairs distance set when both sources are carried by `E`.
Its absolute continuity is therefore sufficient for the conclusion in Theorem 1.1.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
/-- The pushforward of the product measure by Euclidean distance. -/
def crossDistanceMeasure (μ ν : Measure Plane) : Measure ℝ :=
  (μ.prod ν).map (fun p : Plane × Plane ↦ dist p.1 p.2)
instance (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (crossDistanceMeasure μ ν) := by
  unfold crossDistanceMeasure
  infer_instance
end FalconerThetaGauge
