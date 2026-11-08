module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.GaugeFrostmanLimit
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.Asymptotics
public import Mathlib
set_option autoImplicit false
/-!
# Finite logarithmically weighted critical energy

This file proves the finiteness assertion of Corollary 5.5 by summing dyadic
annuli. The inverse distance is taken in the extended nonnegative reals, so the
kernel is infinite on the diagonal. The ball bound implies that the measure
has no atoms, and the diagonal is therefore null in each potential integral.

The annulus decomposition follows `FalconerPacking.Energy` (original source
credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Energy.lean
-/
@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace FalconerThetaGauge
namespace GaugeLogEnergy
open GaugeFrostman
end GaugeLogEnergy
end FalconerThetaGauge
