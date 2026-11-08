/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.DirectionalTestsPiecesPartition
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureEntryPieceLists
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FilteredDistanceMeasureRegularCarriers
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
