module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionLimitOrlicz
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionRay
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionContinuity
public import Mathlib
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
set_option autoImplicit false
/-!
# The actual joint radial measure

The pin/source product is pushed forward by `(x,y) ↦ (x,πₓ(y))`. It equals
the composition-product with the actual radial kernel. For a source density,
its joint density against pin measure times circle arc length is the genuine
polar ray integral. The joint Radon–Nikodym derivative agrees almost everywhere
with the previously defined kernel density.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
/-- The genuine joint radial map retains the pin and projects the source onto the circle. -/
def jointRadialMap (p : Plane × Plane) : Plane × UnitCircle :=
  (p.1, radialProjection p.1 p.2)
/-- The actual joint distribution of the pin and radial source direction. -/
def jointRadialMeasure (μ ν : Measure Plane) : Measure (Plane × UnitCircle) :=
  (μ.prod ν).map jointRadialMap
instance (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (jointRadialMeasure μ ν) := by
  unfold jointRadialMeasure
  infer_instance
end FalconerThetaGauge
