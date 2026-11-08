module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrliczEnergyFourier
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionPolar
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrthogonalProjectionFourierDensity
public import Mathlib
set_option autoImplicit false
/-!
# Orthogonal Fourier slices at the logarithmic endpoint

The projection is the actual inner-product pushforward. Polar coordinates
give its averaged weighted Fourier energy, and reflection yields square
integrability on almost every full line. No power Frostman exponent is assumed.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
def orthogonalProjection (v x : Plane) : ℝ := ⟪x, v⟫
def orthogonalProjectionMeasure (μ : Measure Plane) (v : Plane) : Measure ℝ :=
  μ.map (orthogonalProjection v)
@[fun_prop]
theorem continuous_orthogonalProjection (v : Plane) : Continuous (orthogonalProjection v) := by
  unfold orthogonalProjection
  fun_prop
instance orthogonalProjectionMeasure.instIsProbabilityMeasure (μ : Measure Plane)
    [IsProbabilityMeasure μ] (v : Plane) : IsProbabilityMeasure (orthogonalProjectionMeasure μ v) := by
  unfold orthogonalProjectionMeasure
  infer_instance
end FalconerThetaGauge
