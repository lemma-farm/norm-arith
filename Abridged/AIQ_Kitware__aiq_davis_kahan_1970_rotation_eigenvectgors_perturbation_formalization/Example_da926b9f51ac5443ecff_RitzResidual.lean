module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vb98fefaa4579.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Finite-dimensional spectral subspaces

Restricted spectra, reducing subspaces, canonical spectral projectors, and the
quadratic-form bridges used by finite Davis--Kahan theorems.

The point-spectrum predicates name eigenvalue data explicitly; the quadratic-form results
reduce to the generic bounded spectral-order API after restricting to an invariant subspace.
-/
public section
namespace TauCeti
open scoped InnerProductSpace BigOperators
open Module (finrank)
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- A subspace is **invariant** under an operator when the operator maps it into
itself.

Named for what it says.  It was called `Reduces`, which collided with
`ContinuousLinearMap.Reduces` — a genuinely *stronger* predicate requiring
`Uᗮ` to be invariant too — so one name meant two things in one library and a
reader meeting `IsInvariant A U` in a docstring could not tell which.  For a
symmetric operator the two coincide, and `isInvariant_orthogonal_of_isSymmetric`
is what supplies that; but the implication is one-directional in general, which
is exactly why the names had to be separated. -/
@[expose]
def IsInvariant (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

/-- The finite-dimensional point spectrum of `A` carried by `U`.

For symmetric operators this is the spectrum of the restriction to `U` once
`U` reduces `A`.  The definition avoids exposing a choice of restricted
coordinate space in theorem statements.

Eigenvectors are Mathlib's `Module.End.HasEigenvector` rather than a local predicate; the
only thing a local one added was to fix the eigenvalue as real, which is a property of the
`lam : ℝ` binder here and not of the notion of eigenvector. -/
def restrictedPointSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ Module.End.HasEigenvector A (lam : 𝕜) x}

/-- Every eigenvalue of `A` carried by `U` lies in `Ω`. -/
@[expose]
def PointSpectrumIn (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Ω : Set ℝ) : Prop :=
  restrictedPointSpectrum A U ⊆ Ω

/-- The orthogonal projector onto a finite-dimensional subspace, as a linear
map. -/
@[expose]
noncomputable def projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →ₗ[𝕜] E :=
  ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
/-- The complementary projector. -/
@[expose]
noncomputable def complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection Uᗮ

/-! ### Restriction to an invariant subspace and the restricted-spectrum bridge

These give the concrete restriction `A.restrict hU : U →ₗ[𝕜] U` of an operator to
an invariant subspace and identify its full point spectrum with the `U`-carried
point spectrum of `A`.  This is the bridge used to discharge the spectral
hypotheses of the residual/perturbation `sin Θ` theorems on the subtype. -/

/-! ### Spectral gap ⟹ quadratic-form coercivity bridge

These convert the abstract eigenvalue-set hypotheses (`PointSpectrumIn A U s`) into the
quadratic-form bounds `re ⟪A x, x⟫ ≤ c ‖x‖²` (or `≥`) that the dimension-free
operator-norm Sylvester/`sin Θ` machinery consumes.  This is the point where
finite-dimensional injectivity-surjectivity identifies point and algebra spectra.
The ensuing coercivity estimate is supplied by the generic spectral-order theorem. -/
section SpectralOrder
-- These operator-algebra instances must not change scalar elaboration outside this section.

end SpectralOrder

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vb98fefaa4579.ForTauCeti.Analysis.InnerProductSpace.KyFan ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`KyFan.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).

Ky Fan partial sums of singular values: the trace inequality
`∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{top k} λᵢ(S)` for an orthonormal `k`-family (via a
fractional-knapsack lemma), the Ky Fan variational principle
`∑_{i<k} σᵢ(A) = max re ∑ᵢ ⟪uᵢ, A vᵢ⟫` (via the polar decomposition and the
positive square root), and its consequence, the simultaneous triangle
inequality for all Ky Fan norms — weak majorization
`σ(A + B) ≺_w σ(A) + σ(B)`.
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-! # Ky Fan sums of singular values

For operators on finite-dimensional inner product spaces over `𝕜 = ℝ, ℂ`:

* `kyFanSum k A = ∑_{i<k} σᵢ(A)`, the Ky Fan `k`-sums;
* the **Ky Fan trace inequality**: for a symmetric `S` and an orthonormal
  family `w : Fin k → E`, `∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{i<k} λᵢ(S)`;
* the **Ky Fan variational principle**: `kyFanSum k A` is the maximum of
  `re ∑ᵢ ⟪uᵢ, A vᵢ⟫` over orthonormal `k`-families `u, v`;
* **weak majorization** `kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B` —
  the triangle inequality for every Ky Fan norm simultaneously, the engine of
  the Fan dominance principle (`UnitarilyInvariantSeminorm.lean`);
* unitary invariance, adjoint invariance, and nonnegative-real scaling of
  singular values and Ky Fan sums, plus the bounded-factor domination
  `σᵢ(C ∘ A) ≤ c σᵢ(A)` (Loewner monotonicity of the Gram eigenvalues).

## References

* R. Bhatia, *Matrix Analysis*, Chapter IV (Ky Fan norms, dominance).
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear
  transformations I*, Proc. Nat. Acad. Sci. USA 35 (1949), 652–655.
-/
public section
namespace TauCeti
open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)
variable {𝕜 E F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
/-! ### Singular values under unitaries, scaling, and bounded factors (F0) -/

/-! ### The Ky Fan trace inequality (F1.a–b) -/

/-! ### The Ky Fan variational principle (F1.c) -/

/-! ### Ky Fan sums and weak majorization (F2)

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.KyFan`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `199390a`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/
/-- **The Ky Fan `k`-sum** of an operator: the sum of its `k` largest singular
values.  `kyFanSum 1 A = ‖A‖`, `kyFanSum (finrank 𝕜 E) A` is the trace norm.

`@[expose]`: the defining sum is the working form throughout the Ky Fan and
unitarily-invariant-norm development, so the body must stay visible to the
kernel for the `rfl`-level rewrites below. -/
@[expose]
noncomputable def kyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vb98fefaa4579.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Directed principal-angle geometry

Canonical finite-dimensional cosine, sine, angle, tangent, and double-angle
objects, together with their singular-value and projector dictionaries.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Core/AngleGeometry.lean`
before the dependency-closed base of the sin-Θ core moved into the staging
layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/
public section
namespace TauCeti
open scoped InnerProductSpace BigOperators
open Module (finrank)
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
section OperatorAbsSingularValues
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

end OperatorAbsSingularValues
/-- The cosine cross-projection `P_V P_U`. -/
@[expose]
noncomputable def cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection V ∘ₗ projection U
/-- The sine cross-projection `P_{Vᗮ} P_U`. -/
@[expose]
noncomputable def sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  complementaryProjection V ∘ₗ projection U

/-- Principal-angle sines: the singular values of the directed cross projection
`P_{Vᗮ} P_U`.  In equal-dimension configurations these are the sines of the
principal angles; when `dim U ≠ dim V` the directed map also records the
`π/2` "defect" directions, so this is not symmetric in `U, V` in general. -/
@[expose]
noncomputable def principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (sinThetaMap U V : E →ₗ[𝕜] E).singularValues
/-- Principal angles as a sorted finitely supported sequence: `arcsin` applied to
the principal sines.  `arcsin 0 = 0` keeps the support finite. -/
noncomputable def principalAngles (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (principalSines U V).mapRange Real.arcsin Real.arcsin_zero
/-- Principal-angle tangents: `tan` applied to the principal angles.  `tan 0 = 0`
keeps the support finite (poles at `π/2` are only reached in the non-acute
configuration, excluded by the tangent theorems' hypotheses). -/
noncomputable def principalTangents (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (principalAngles U V).mapRange Real.tan Real.tan_zero

/-- The pair has no angle `π/2`; equivalently, `P_V` is injective on `U`. -/
@[expose]
def IsTransverse (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection] : Prop :=
  ∀ x ∈ U, V.starProjection x = 0 → x = 0

/-! ### Reading the principal-angle sequence on a basis of the source subspace

`cosThetaMap U V = P_V P_U` and `sinThetaMap U V = P_{Vᗮ} P_U` both vanish on
`Uᗮ`, so restricting their domain to `U` loses nothing: the singular-value
sequence is unchanged.  Combined with the Frobenius identity
`∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²` (`sum_sq_singularValues`), this reads the squared
principal cosines and sines as ordinary sums over an orthonormal basis of `U`,
with **no** basis of the ambient space and no trace machinery. -/
section SourceBasis
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

end SourceBasis
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vb98fefaa4579.ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Ritz compression and residual

Finite-dimensional compressions, invariant-pair residuals, Galerkin
orthogonality, covariance, and Frobenius minimality.

## Sources

Ritz compressions and their residuals are the numerical-analysis form of the
Davis--Kahan `sin Θ` theorem; the source argument is distilled in
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex` and
`prose/distilled_literature/DavisKahan1970_part_III.tex`.  The generic-trial-map
shape here is this library's, not the paper's.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Residual/Ritz.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/
public section
namespace TauCeti
open scoped InnerProductSpace BigOperators
open Module (finrank)
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Compression of `A` to the isometric coordinate space of `X`. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] F :=
  X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap
/-- Residual of an approximate invariant pair represented by an isometric
embedding. -/
@[expose]
noncomputable def residual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M
/-- Galerkin/Ritz residual. -/
noncomputable def ritzResidual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] E :=
  residual A X (compression A X)
/-- The represented approximate subspace. -/
@[expose]
def approximateSubspace (X : F →ₗᵢ[𝕜] E) : Submodule 𝕜 E :=
  LinearMap.range X.toLinearMap

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vb98fefaa4579.ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Principal-angle embeddings for trial subspaces

Coordinate-space sine and cosine embeddings, their projected residual identity,
and the singular-value dictionary relating them to directed principal angles.

## Sources

Principal angles between subspaces and their use in a residual bound follow
Davis--Kahan; see
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex` and
`prose/distilled_literature/DavisKahan1970_part_III.tex`.  The trial-subspace
embedding shape is this library's.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Residual/AngleEmbedding.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/
public section
namespace TauCeti
open scoped InnerProductSpace BigOperators
open Module (finrank)
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Sine map from approximate coordinates into the orthogonal complement of
an exact subspace. -/
@[expose]
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  complementaryProjection U ∘ₗ X.toLinearMap

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vb98fefaa4579.ForTauCeti.Analysis.InnerProductSpace.Singular.System ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Intrinsic singular systems for rectangular linear maps

A reusable singular-vector layer stated directly for a linear map between finite-dimensional
`RCLike` inner-product spaces.  The right singular basis is the sorted orthonormal eigenbasis
of `A†A`; left singular vectors are the normalized images `σᵢ⁻¹ • A vᵢ`.

## Main results

* `TauCeti.apply_rightSingularBasis_eq_smul_leftSingularVector`: the singular relation
  `A vᵢ = σᵢ • uᵢ`, including the zero case;
* `TauCeti.orthonormal_leftSingularVector_subtype`: left singular vectors attached to
  nonzero singular values are orthonormal;
* `TauCeti.selfCompAdjoint_apply_leftSingularVector`: nonzero left singular vectors are
  eigenvectors of `AA†` with eigenvalue `σᵢ²`;
* `TauCeti.singular_reconstruction` and `TauCeti.eq_sum_singularValue_rankOne`: the
  intrinsic singular expansion of `A`;
* `TauCeti.exists_orthonormalBasis_extending_leftSingularVector`: the nonzero left
  singular family extends to an orthonormal basis of the codomain.

## Proof sources

The construction parallels the Apache-2.0 matrix-Euclidean development in
`vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean` (Zhang–Lee–Liu),
restated intrinsically for linear maps; the excerpt was used as a route map and no code was
copied verbatim.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SingularSystem`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `82d20de`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 High, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/
public section
namespace TauCeti
open Module LinearMap
open scoped InnerProductSpace
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
/-- The right singular basis, chosen as the sorted orthonormal eigenbasis of `A†A`. -/
noncomputable def rightSingularBasis (A : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
/-- The total left singular-vector expression `σᵢ⁻¹ • A vᵢ`.

At a zero singular value this definition evaluates to zero because division in a field is
total. Orthonormality is asserted only on the subtype of nonzero singular values. -/
noncomputable def leftSingularVector (A : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) : F :=
  (((A.singularValues i : ℝ) : 𝕜)⁻¹) • A (rightSingularBasis A i)

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_da926b9f51ac5443ecff_RitzResidual ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
/-!
# The paper-exact finite Davis--Kahan `tan Θ` theorem

This module records the finite residual theorem in the exact orientation used
in Davis--Kahan (1970), Section 2 and equation (6.6): the Ritz compression lies
in a finite interval, while the unwanted exact spectrum lies above that
interval by `δ`.  The conclusion controls every unitarily invariant norm.

The proof is organized around the source argument.  The hard root is a family
of Ky Fan prefix inequalities obtained from singular vectors of the sine block;
Fan dominance then gives every rectangular unitarily invariant norm.  This is
intentionally separate from the later relaxed spectral-norm theorem and from
an ordered graph-Sylvester formulation.
-/
namespace TauCeti
namespace DavisKahan.FiniteDimensional
open scoped InnerProductSpace BigOperators
open Module (finrank)
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- The one-sided interval hypothesis in the original `tan Θ` theorem.

The Ritz compression of `A` to the trial coordinates is contained in
`[β, α]`, while the spectrum of `A` carried by the orthogonal complement of
the exact subspace is contained in `[α + δ, ∞)`. -/
def TanThetaIntervalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (β α δ : ℝ) : Prop :=
  PointSpectrumIn (compression A X) ⊤ (Set.Icc β α) ∧
    PointSpectrumIn A Uᗮ (Set.Ici (α + δ))

/-- The normalized residual-side witness attached to a sine singular vector.

At a zero singular value the tangent contribution is zero, so the corresponding Ritz-space
basis vector is used.  At a positive singular value, the left singular vector is projected
away from the Ritz space and normalized by the complementary cosine. -/
noncomputable def tanThetaResidualWitness
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) (i : Fin (finrank 𝕜 F)) : E :=
  let S := sinThetaEmbedding U X
  let σ := S.singularValues i
  let v := rightSingularBasis S i
  if σ = 0 then X v else
    (((Real.sqrt (1 - σ ^ 2) : ℝ) : 𝕜)⁻¹) •
      (leftSingularVector S i - ((σ : ℝ) : 𝕜) • X v)


set_option linter.unusedVariables false in
/-- Ky Fan domination up to the full trial-space dimension. -/
private theorem kyFan_tanTheta0_ritzResidual_le_of_le_finrank
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U)
    {k : ℕ} (hk : k ≤ finrank 𝕜 F) 
    (h_TauCeti_DavisKahan_FiniteDimensional_orthonormal_tanThetaResidualWitness : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      (U : Submodule 𝕜 E) [inst_7 : U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E),
      TauCeti.IsTransverse (TauCeti.approximateSubspace X) U →
        Orthonormal 𝕜 (TauCeti.DavisKahan.FiniteDimensional.tanThetaResidualWitness U X))
    (h_TauCeti_sum_le_kyFanSum_of_orthonormal : ∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] [inst_4 : NormedAddCommGroup F]
      [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F] {A : E →ₗ[𝕜] F} {k : ℕ},
      k ≤ Module.finrank 𝕜 E →
        ∀ {u : Fin k → F} {v : Fin k → E},
          Orthonormal 𝕜 u →
            Orthonormal 𝕜 v →
              ∀ {t : Fin k → ℝ},
                (∀ (i : Fin k), t i ≤ (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 (u i) ((A : E → F) (v i)))) →
                  ∑ i : Fin k, t i ≤ TauCeti.kyFanSum k A)
    (h_TauCeti_DavisKahan_FiniteDimensional_tanThetaResidualWitness_scalar : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      {A : E →ₗ[𝕜] E},
      A.IsSymmetric →
        ∀ {U : Submodule 𝕜 E} [inst_7 : U.HasOrthogonalProjection],
          TauCeti.IsInvariant A U →
            ∀ (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.FiniteDimensional.TanThetaIntervalGap A U X β α δ →
                  ∀ (tanTheta0 : F →ₗ[𝕜] E),
                    tanTheta0.singularValues =
                        TauCeti.principalTangents (TauCeti.approximateSubspace X) U →
                      ∀ (i : Fin (Module.finrank 𝕜 F)),
                        δ * (tanTheta0.singularValues : ℕ → ℝ) (↑i : ℕ) ≤
                          (RCLike.re : 𝕜 → ℝ)
                            (Inner.inner 𝕜
                              (TauCeti.DavisKahan.FiniteDimensional.tanThetaResidualWitness U X i)
                              ((TauCeti.ritzResidual A X : F → E)
                                ((TauCeti.rightSingularBasis (TauCeti.sinThetaEmbedding U X) :
                                    Fin (Module.finrank 𝕜 F) → F)
                                  i))))
    (h_TauCeti_DavisKahan_FiniteDimensional_isTransverse_of_tanThetaIntervalGap : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      {A : E →ₗ[𝕜] E},
      A.IsSymmetric →
        ∀ {U : Submodule 𝕜 E} [inst_7 : U.HasOrthogonalProjection],
          TauCeti.IsInvariant A U →
            ∀ (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.FiniteDimensional.TanThetaIntervalGap A U X β α δ →
                  TauCeti.IsTransverse (TauCeti.approximateSubspace X) U)
    :
    δ * TauCeti.kyFanSum k tanTheta0 ≤
      TauCeti.kyFanSum k
        (ritzResidual A X) := by
  let S := sinThetaEmbedding U X
  let castIndex : Fin k → Fin (finrank 𝕜 F) := fun i => Fin.castLE hk i
  have htrans := h_TauCeti_DavisKahan_FiniteDimensional_isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap
  have huFull := h_TauCeti_DavisKahan_FiniteDimensional_orthonormal_tanThetaResidualWitness U X htrans
  have hu : Orthonormal 𝕜
      (fun i : Fin k => tanThetaResidualWitness U X (castIndex i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp huFull (castIndex i) (castIndex j))
  have hv : Orthonormal 𝕜
      (fun i : Fin k => rightSingularBasis S (castIndex i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp (rightSingularBasis S).orthonormal
        (castIndex i) (castIndex j))
  have hsum := h_TauCeti_sum_le_kyFanSum_of_orthonormal
    hk hu hv (fun i =>
      h_TauCeti_DavisKahan_FiniteDimensional_tanThetaResidualWitness_scalar hA hU X hδ hgap tanTheta0 htan (castIndex i))
  unfold TauCeti.kyFanSum
  rw [Finset.mul_sum]
  exact hsum
end DavisKahan.FiniteDimensional
end TauCeti
