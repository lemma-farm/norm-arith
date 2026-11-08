/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.OperatorAngle
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import Mathlib
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.MetricSpace.Antilipschitz
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Graph subspaces and angular operators

Literature writeup: local TeX, Sections 16--17.  This is the geometric bridge
between projection estimates and operator Riccati equations.
-/
/-! ## Construction plan

* Define the graph subspace as the range of `x |-> (x, X x)` under the
  orthogonal-sum equivalence; for an ambient decomposition, transport this
  construction through `U x Uperp ~= E`.
* Prove the graph projection formula by solving the normal equations.  The
  diagonal factors are `(1+X⋆X)^{-1}` and `(1+XX⋆)^{-1}` and are positive
  invertible.
* Derive the graph/angular correspondence from transversality of the first
  coordinate projection, then identify the graph norm with tangent of the
  operator angle.
-/
/-! ## Donor API audit and execution plan

The graph-subspace vendor survey is recorded in
`dev/graph-subspace-vendor-survey-2026-07-14.md`.  The immediate proof should
reuse the pinned Mathlib APIs below rather than rebuilding closed-range or
inverse-continuity arguments locally.

Work with subtype maps rather than ambient formulas first.  Define the graph
embedding from `U` to `E` by `u ↦ u + X u`, where `IsAngularOperator U X`
ensures `X u ∈ Uᗮ`.  The Pythagorean identity gives a one-antilipschitz bound.
Use `AntilipschitzWith.isClosed_range` to obtain closedness of the range, then
the standard closed-subspace projection instance.

For acute-to-graph, restrict `projection U` to `V`.  The preferred inverse
routes are:

* `ContinuousLinearMap.equivRange` after injectivity and closed range are known;
* `ContinuousLinearEquiv.ofBijective` after direct injectivity and surjectivity;
* `Units.oneSub` for the near-identity compression when the acute norm bound
  yields an operator of norm strictly below one.

`LinearPMap.graph` and `LinearPMap.IsClosed` are the canonical graph language
for later alignment with the unbounded appendix.  The bounded graph may be
implemented first as a continuous-map range, but its comparison with the
`LinearPMap` graph should be explicit rather than introducing a second
unrelated graph notion.

The current unconditional projection instance for `graphSubspace U X` is a
signature defect: an arbitrary ambient `X` need not give a closed graph range.
The implementation pass must either add `hX : IsAngularOperator U X` to that
instance or bundle angularity into the graph object before closing it.

For the projection formula, define
`G := I + X.adjoint ∘L X` on `U`.  Prove `G ≥ I`, hence invertible, before
mentioning `G⁻¹` or `G⁻¹/²`.  Construct the normalized graph isometry
`J := graphEmbedding ∘ G⁻¹/²`; then the projection is `J ∘L J.adjoint`.
Expand this identity blockwise and only afterward package the ambient
`graphProjectionFormula`.
-/
namespace TauCeti
open TauCeti
namespace DavisKahanExt
open DavisKahan
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
/-- Graph subspace over `U` with angular operator `X`.

Defined as the topological closure of the parametrized graph range
`{P_U x + X (P_U x) | x}`, matching the range convention of
`acute_iff_exists_bounded_angularOperator`.  Taking the closure makes the
orthogonal-projection instance below unconditional; for an angular operator
the graph embedding is bounded below, its range is already closed, and the
closure adds nothing. -/
noncomputable def graphSubspace (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Submodule 𝕜 E :=
  (LinearMap.range
    (projection U + X ∘L projection U).toLinearMap).topologicalClosure
/-- The graph of a bounded operator is orthogonally complemented, being closed. -/
noncomputable instance graphSubspace_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : (graphSubspace U X).HasOrthogonalProjection := by
  have : CompleteSpace (graphSubspace U X) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _
variable {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] {X : E →L[𝕜] E}
end DavisKahanExt
end TauCeti