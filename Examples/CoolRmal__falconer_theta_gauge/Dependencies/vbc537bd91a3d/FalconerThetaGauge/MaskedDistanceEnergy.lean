module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.FilteredDistanceMeasureGeometry
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.ScalarEnergyBinningFourier
public import Mathlib
set_option autoImplicit false
/-! # The actual passing weighted distance measure and energy of Definition 7.2 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal
namespace FalconerThetaGauge
/-- The literal weighted distance pushforward of passing pairs in the two actual carriers. -/
def passingWeightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) : Measure ℝ :=
  filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y) (Z.indicator (fun _ ↦ 1))
instance instSFinitePassingWeightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane) (Z : Set (Plane × Plane)) :
    SFinite (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
  unfold passingWeightedDistanceMeasure filteredCrossDistanceMeasure
  infer_instance
end FalconerThetaGauge
