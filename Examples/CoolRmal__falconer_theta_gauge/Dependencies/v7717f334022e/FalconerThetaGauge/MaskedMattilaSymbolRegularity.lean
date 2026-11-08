module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedMattilaPointwiseInversion
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ScheduledSymbolBudget
public import Mathlib
set_option autoImplicit false
/-! # Genuine built-symbol amplitudes for the pointwise masked Mattila inversion -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
def builtSymbolAngularAmplitude (b : Plane → UnitCircle → ℝ) (x : Plane) : ℝ → ℂ :=
  fun θ ↦ (b x (unitCircleOfAngle θ) : ℂ)
def builtSymbolPairAngularAmplitude (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x y : Plane) : ℝ → ℂ := builtSymbolAngularAmplitude b₁ x * builtSymbolAngularAmplitude b₂ y
end FalconerThetaGauge
