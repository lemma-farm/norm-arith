module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionLimit
public import Mathlib
public import Mathlib.Analysis.PSeries
set_option autoImplicit false
/-!
# Quantitative tails of the limiting Radon–Nikodym density

The open-set cutoff estimate gives a logarithmic tail bound for the actual
Radon–Nikodym derivative. These tails preserve lower logarithmic Orlicz
moments when the approximating densities have a stronger moment.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
