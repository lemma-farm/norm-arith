/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingFarSum
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingIntegratedKernel
public import Mathlib
set_option autoImplicit false
/-! # Actual far kernel integration, with true distance weights and true passing sets -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
