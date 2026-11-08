/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureExcessGauge
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularDecompositionMeasures
public import Mathlib
set_option autoImplicit false
/-!
# Actual excess properties and occupied-cell counts of retained parts

The normalized retained carriers satisfy Lemma 5.10, and their occupied
descendants satisfy the counting estimate (5.2).
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
