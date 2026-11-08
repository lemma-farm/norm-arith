module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.FilteredDistanceMeasureGeometry
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.FilteredDistanceMeasureCircle
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionSpread
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrliczSmallSet
public import Mathlib
set_option autoImplicit false
/-!
# Actual bad-direction pairs and their Orlicz mass bound

Bad sets are Borel subsets of the pin/circle product. Their sections are the
actual excluded directions at each pin. This retains the joint measurability
needed for the product measure, rather than postulating a bound on pair mass.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
