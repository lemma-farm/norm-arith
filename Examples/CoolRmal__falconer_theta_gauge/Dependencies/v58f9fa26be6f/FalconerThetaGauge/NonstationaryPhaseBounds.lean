/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The real-to-complex derivative identity is adapted from falconer-packing;
the factorial transport bound is new. See docs/ATTRIBUTION.md.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.NonstationaryPhase
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularFunctions
public import Mathlib
set_option autoImplicit false
/-!
# Factorial bounds for repeated nonstationary transport

The exact derivative orders are retained in each Leibniz term. This gives a
polynomial base raised to the transport order, as required by the shrinking
parameter proof.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped ContDiff
namespace FalconerThetaGauge
end FalconerThetaGauge
