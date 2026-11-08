module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsWidening
public import Mathlib
public import Mathlib.Data.Int.Interval
set_option autoImplicit false
/-!
# Exact nine-square dyadic disc cover

A closed disc of radius one generation-`d` side length lies in the nine
half-open squares neighboring the square of its center. Floor indices handle
all boundary points without a nonatomicity assumption.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
