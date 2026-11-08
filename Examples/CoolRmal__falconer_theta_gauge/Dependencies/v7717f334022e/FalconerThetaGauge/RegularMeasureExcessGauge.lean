/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureExcess
public import Mathlib
set_option autoImplicit false
/-!
# The gauge lower bound for the actual excess function

A generation-`n` cube fits in the open ball of radius `2^(-n)` about its
midpoint. The gauge estimate and the retained part's actual mass give the
lower excess barrier with the exact normalization cost.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeLogEnergy GaugeSeparatedMeasures
end FalconerThetaGauge
