/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.DirectionalTestsPiecesPartition
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureEntryPieceLists
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.FilteredDistanceMeasureRegularCarriers
public import Mathlib
set_option autoImplicit false
/-! # Literal regular-piece carriers lie in occupied cells at every listed anchor -/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
