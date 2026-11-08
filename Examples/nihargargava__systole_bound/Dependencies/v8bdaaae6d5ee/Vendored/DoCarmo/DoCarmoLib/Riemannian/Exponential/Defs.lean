module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Exponential/Defs.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Existence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.MaximalInterval
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Uniqueness
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream overlapping finite-dimensional instance binders.
set_option linter.overlappingInstances false
/-!
# The exponential map of a smooth Riemannian metric

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, and for every base point
`p : M` and tangent vector `v : T_p M`, the maximal geodesic
`maximalGeodesic g p v : ℝ → M` provides a canonical curve through `p`
with initial velocity `v`. The exponential map at `p` is the value of
this curve at time `t = 1`.

## Main definitions

* `expMap g p v` — the exponential map at `p` applied to `v`, defined as
  `maximalGeodesic g p v 1`. On the natural domain (`expDomain g p`),
  this is the genuine geodesic-flow value; outside, it reduces to the
  constant junk value `p` inherited from `maximalGeodesic_of_not_mem`.

* `expDomain g p` — the natural domain of `expMap g p`: the set of
  vectors `v : T_p M` such that the maximal interval contains `1`.

## Main theorems

* `expMap_zero` — the exponential map sends the zero tangent vector to its
  base point: `expMap g p 0 = p`. The proof propagates uniqueness of the
  stationary integral curve across the connected maximal-geodesic witness.

* `zero_mem_expDomain` — the zero vector is always in `expDomain g p`,
  since the stationary geodesic exists for all time.

* `expDomain_nonempty` — the natural domain is non-empty.

The full openness of `expDomain g p` at every `v ∈ expDomain g p`
requires joint smoothness of the geodesic flow in `(t, v)`. The joint
initial-condition regularity of the chart-pushed geodesic flow is developed in
`Geodesic/FlowC1Dependence.lean` and `Geodesic/FlowCInftyDependence.lean`;
lifting it back through charts to obtain openness at non-zero `v` is a downstream
step and is not addressed here.
-/
noncomputable section
open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff
namespace Riemannian
namespace Exponential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open Riemannian.Geodesic
section StationaryWitness
variable [I.Boundaryless]
end StationaryWitness
section JunkValue
variable [I.Boundaryless]
end JunkValue
section ExpMapZeroWitnessLevel
variable [I.Boundaryless]
end ExpMapZeroWitnessLevel
section ZeroVelocityPropagation
variable [I.Boundaryless]
  [T2Space (TangentBundle I M)]
end ZeroVelocityPropagation
section ExpMapZero
variable [I.Boundaryless]
  [T2Space (TangentBundle I M)]
end ExpMapZero
end Exponential
end Riemannian
end
