/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Smooth reciprocal construction adapted from falconer-packing; see docs/ATTRIBUTION.md.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.NonstationaryReciprocal
public import Mathlib
set_option autoImplicit false
/-!
# A smooth reciprocal with uniform derivative bounds

The reciprocal is cut off near zero. Its derivatives are bounded on a fixed compact interval;
outside that interval they are exactly the derivatives of the ordinary reciprocal.
-/
@[expose] public section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
