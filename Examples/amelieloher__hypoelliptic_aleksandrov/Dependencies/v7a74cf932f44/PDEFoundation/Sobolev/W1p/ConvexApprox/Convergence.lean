module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.ConvexApprox.PointwiseBounds
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# `L^p` convergence of convex-domain smoothing

This file proves value convergence for convex approximation. Continuous input
is handled first by uniform convergence on the bounded domain. Density of
bounded continuous functions then gives convergence for arbitrary
`MemLpOn U p` input when `1 ≤ p < ∞`.

The final weighted statements show that
`(1 - ε) * convexApproxSmoothing ...` has the same `L^p` limit. This is the
form consumed by the weak-gradient approximation layer.

The classical-input derivative route is deliberately absent: weak derivatives
are handled separately without making that route a dependency of value
convergence.
-/
@[expose] public section
open scoped ENNReal Pointwise Convolution Topology
namespace PDE
open Filter MeasureTheory
end PDE
