module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpCircle
public import Mathlib
set_option autoImplicit false
/-!
# Jointly Borel masks from the actual finite partition into occupied anchor cells

At a fixed scale the angular test data are constant on each occupied anchor cell.
Constructing each circle mask first and then taking this finite Borel partition
avoids any unjustified measurability claim for arbitrary varying set fibers.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
end FalconerThetaGauge
