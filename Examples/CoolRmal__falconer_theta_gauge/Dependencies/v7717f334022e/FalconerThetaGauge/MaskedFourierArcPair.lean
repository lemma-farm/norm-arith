module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedFourierRadialMeasure
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.EqualArcCutoff
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FiniteGraphSchurIntegral
public import Mathlib
set_option autoImplicit false
/-! # Actual square-root arc amplitudes in the finite joint Fourier measure -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace FalconerThetaGauge
/-- The actual radial and two-circle product measure, with no hypothetical energy input. -/
def maskedFourierJointMeasure (K v : ℕ) : Measure (ℝ × UnitCircle × UnitCircle) :=
  (maskedFourierRadialMeasure K v).prod (circleArcLength.prod circleArcLength)
instance isFiniteMeasure_maskedFourierJointMeasure (K v : ℕ) :
    IsFiniteMeasure (maskedFourierJointMeasure K v) := by
  unfold maskedFourierJointMeasure
  infer_instance
end FalconerThetaGauge
