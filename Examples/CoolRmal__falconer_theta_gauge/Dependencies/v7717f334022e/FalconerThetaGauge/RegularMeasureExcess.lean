/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureExcessMass
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.Parameters
public import Mathlib
set_option autoImplicit false
/-!
# The actual excess function of a unit-square probability

The definition uses the largest actual cell mass. Dyadic refinement gives the
exact Lipschitz constant `1/N`, independently of regular decomposition.
-/
@[expose] public section
noncomputable section
open MeasureTheory
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
