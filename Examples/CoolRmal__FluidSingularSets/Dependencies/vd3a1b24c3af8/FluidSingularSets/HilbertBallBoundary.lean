-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.FluidSingularSets.PolynomialBallMeanInverse
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Genuine zero-boundary energy membership of the weighted ball fields

The interior compact test gradients converge strongly in actual `L²` to the
gradient of the weighted smooth field. Closure of the constructed Stokes test
gradient space therefore supplies genuine zero-boundary energy membership.
-/
@[expose] public section
open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
