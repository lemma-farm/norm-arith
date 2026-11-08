module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionDefinitions
public import Mathlib
set_option autoImplicit false
/-!
# Polar integration in the Euclidean plane

The exact Jacobian formula is transferred from Mathlib's complex polar coordinates
by the volume-preserving standard real linear isometry. The transfer follows
`FalconerPacking.PolarFourierEnergy` (original source credits Yongxi Lin, Apache 2.0),
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/PolarFourierEnergy.lean
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
