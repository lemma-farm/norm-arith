-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v7b8c5b595918.FluidSingularSets.PolynomialBallDensity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Actual mean-zero polynomial density and divergence range

The ball integral is a genuine bounded Hilbert functional. Removing the actual
ball mean projects onto its closed kernel. Polynomial density is preserved by
this projection, and compact test integration proves that every completed
zero-boundary divergence belongs to the same kernel.
-/
@[expose] public section
open CKN MvPolynomial MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
