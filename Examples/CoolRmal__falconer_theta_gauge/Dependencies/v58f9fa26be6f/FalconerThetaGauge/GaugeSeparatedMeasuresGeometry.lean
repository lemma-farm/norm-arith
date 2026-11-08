module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeSeparatedMeasuresSimilarity
public import Mathlib
set_option autoImplicit false
/-!
# The fixed geometric normalization in Proposition 5.6

An explicit positive similarity places the centers one quarter apart around the
center of the unit square. The selected compact pieces lie in discs of radius
one four-hundredth, and their pair distances lie between `0.24` and `0.26`.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace FalconerThetaGauge
namespace GaugeSeparatedMeasures
/-- The half-open unit square, with its coordinate description. -/
def unitSquare : Set Plane := {x | ∀ i : Fin 2, x i ∈ Ico (0 : ℝ) 1}
end GaugeSeparatedMeasures
end FalconerThetaGauge
