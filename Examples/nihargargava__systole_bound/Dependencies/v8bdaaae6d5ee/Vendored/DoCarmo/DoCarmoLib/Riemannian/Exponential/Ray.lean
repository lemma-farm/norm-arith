module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Exponential/Ray.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.Defs
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.InitialVelocity
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream overlapping finite-dimensional instance binders.
set_option linter.overlappingInstances false
/-!
# The exponential map along rays

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the exponential map traces the
geodesic along each ray of the tangent space:

`exp_p (t • v) = γ(t, p, v)`.

This is do Carmo's description "`exp_q v` is obtained by going a length `|v|`
from `q` along the geodesic with velocity `v / |v|`" (Ch. 3, after Prop. 2.7),
and it is the computational heart of `d(exp_p)_0 = id` (Ch. 3, Prop. 2.9): the
curve `t ↦ exp_p (t v)` *is* the geodesic `t ↦ γ(t, p, v)`, so its velocity at
`t = 0` is `v`.

The chart-validity clause `hsrc` is inherited from the value-level homogeneity
`maximalGeodesic_fiberScale`: the canonical maximal geodesic is built from the
chart-`p`-fixed spray, which degenerates off the chart at `p`.
-/
noncomputable section
open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff
namespace Riemannian
namespace Exponential
open Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]
end Exponential
end Riemannian
end
