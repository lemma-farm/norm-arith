/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureEntry
public import Mathlib
set_option autoImplicit false
/-!
# The entry properties of actual retained regular pieces

The exact parameter facts, actual gauge lower barrier and largest-cell excess
give all three conclusions of Lemma 9.2, including the long interval and its
post-entry budget.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
