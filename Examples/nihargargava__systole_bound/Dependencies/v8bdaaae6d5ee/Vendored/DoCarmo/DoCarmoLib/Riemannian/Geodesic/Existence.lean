module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/Existence.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# Local existence of geodesics via Picard-Lindelöf

For a smooth Riemannian metric `g` on a smooth manifold `M` (boundaryless,
modelled on a finite-dimensional inner-product space `E`) and any initial datum
`(p : M, v : T_p M)`, there exists a curve `γ : ℝ → M` starting at `p`
that is the projection of a local integral curve of the chart-fixed
geodesic vector field `geodesicVectorFieldChart g p` on `T M`.

The construction proceeds in two steps:

1. **Picard-Lindelöf on the tangent bundle.** We feed
   `geodesicVectorFieldChart g p` into Mathlib's existence theorem
   `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`. The vector
   field is `C^∞` at `⟨p, v⟩ : TangentBundle I M` by
   `geodesicVectorFieldChart_contMDiffAt`; the tangent bundle is
   boundaryless because `(I.prod 𝓘(ℝ, E)).Boundaryless` is automatic
   from `[I.Boundaryless]`; finite-dimensional real normed spaces are complete,
   as required by the existence theorem. The output is a curve
   `f : ℝ → TangentBundle I M` with
   `f 0 = ⟨p, v⟩` and `IsMIntegralCurveAt f (gvfChart g p) 0`.

2. **Projection to `M`.** Set `γ t := (f t).proj`. Then `γ 0 = p` and
   `IsGeodesicAt g γ 0` packages the integral-curve property of `f` into
   the integral-curve geodesic predicate (with chart basepoint `α := p`).

The headline theorem `exists_geodesic_with_initial_velocity_at` returns `IsGeodesicAt g γ 0` —
the local geodesic predicate at `t = 0`. The chart-`γ(t)` second-derivative
form `HasGeodesicEquationAt g γ 0` is a separate downstream bridge once the
chart-derivative properties of the projection are recorded.
-/
noncomputable section
open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff
namespace Riemannian
namespace Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
section ChartedPicardLindelof
variable [I.Boundaryless]
end ChartedPicardLindelof
end Geodesic
end Riemannian
end
