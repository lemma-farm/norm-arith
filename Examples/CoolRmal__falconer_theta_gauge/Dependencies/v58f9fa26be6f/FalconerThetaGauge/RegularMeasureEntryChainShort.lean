/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularMeasureEntryChainCount
public import Mathlib
set_option autoImplicit false
/-!
# Exact short-chain bounds at the manuscript's parameters

For the actual six transition types, ordinary moves number at most `7 / κ`
and low-frequency children at most `1 / ε`. These are conclusions of the
concrete scheduled-test chain, rather than hypotheses about its counts.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
namespace ProfileMoveChain
end ProfileMoveChain
end FalconerThetaGauge
