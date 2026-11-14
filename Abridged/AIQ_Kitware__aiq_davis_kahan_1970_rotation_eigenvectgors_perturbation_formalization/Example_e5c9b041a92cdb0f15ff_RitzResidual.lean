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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vcd1fadb461b5.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vcd1fadb461b5.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vcd1fadb461b5.ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vcd1fadb461b5.ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vcd1fadb461b5.ForTauCeti.Analysis.InnerProductSpace.Singular.System ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_e5c9b041a92cdb0f15ff_RitzResidual ====
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
/-- The scalar spectral-gap estimate for one principal tangent.

This is the analytic core of equation (6.6), expressed without direct-rotation coordinates.
The left singular vector of the sine block is projected away from the Ritz space; Galerkin
orthogonality removes that projection from the residual pairing, while its norm supplies the
cosine denominator. -/
theorem tanThetaResidualWitness_scalar
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U)
    (i : Fin (finrank 𝕜 F)) 
    (h_TauCeti_orthonormal_leftSingularVector_subtype : ∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] [inst_4 : NormedAddCommGroup F]
      [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F),
      Orthonormal 𝕜
        fun (i : { j : Fin (Module.finrank 𝕜 E) // (A.singularValues : ℕ → ℝ) (↑j : ℕ) ≠ 0 }) ↦
        TauCeti.leftSingularVector A (↑i : Fin (Module.finrank 𝕜 E)))
    (h_TauCeti_sylvester_sinThetaEmbedding_eq_projectedResidual : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] {F : Type u_3} [inst_3 : NormedAddCommGroup F]
      [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ[𝕜] E},
      A.IsSymmetric →
        ∀ {U : Submodule 𝕜 E} [inst_5 : U.HasOrthogonalProjection],
          TauCeti.IsInvariant A U →
            ∀ (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F),
              A ∘ₗ TauCeti.sinThetaEmbedding U X - TauCeti.sinThetaEmbedding U X ∘ₗ M =
                TauCeti.complementaryProjection U ∘ₗ TauCeti.residual A X M)
    (h_TauCeti_DavisKahan_FiniteDimensional_principalTangents_approximateSubspace_apply : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      (U : Submodule 𝕜 E) [inst_7 : U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) (i : ℕ),
      (TauCeti.principalTangents (TauCeti.approximateSubspace X) U : ℕ → ℝ) i =
        Real.tan (Real.arcsin (((TauCeti.sinThetaEmbedding U X).singularValues : ℕ → ℝ) i)))
    (h_TauCeti_upperFormBound_of_pointSpectrumIn : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E},
      A.IsSymmetric →
        ∀ {U : Submodule 𝕜 E},
          TauCeti.IsInvariant A U →
            ∀ {c : ℝ},
              TauCeti.PointSpectrumIn A U (Set.Iic c) →
                ∀ x ∈ U, (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 ((A : E → E) x) x) ≤ c * ‖x‖ ^ 2)
    (h_TauCeti_apply_rightSingularBasis_eq_smul_leftSingularVector : ∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] [inst_4 : NormedAddCommGroup F]
      [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F)
      (i : Fin (Module.finrank 𝕜 E)),
      (A : E → F) ((TauCeti.rightSingularBasis A : Fin (Module.finrank 𝕜 E) → E) i) =
        (↑((A.singularValues : ℕ → ℝ) (↑i : ℕ)) : 𝕜) • TauCeti.leftSingularVector A i)
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
    (h_TauCeti_isSymmetric_compression : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      {A : E →ₗ[𝕜] E}, A.IsSymmetric → ∀ (X : F →ₗᵢ[𝕜] E), (TauCeti.compression A X).IsSymmetric)
    (h_TauCeti_lowerFormBound_of_pointSpectrumIn : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E},
      A.IsSymmetric →
        ∀ {U : Submodule 𝕜 E},
          TauCeti.IsInvariant A U →
            ∀ {c : ℝ},
              TauCeti.PointSpectrumIn A U (Set.Ici c) →
                ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 ((A : E → E) x) x))
    (h_TauCeti_adjoint_comp_ritzResidual_eq_zero : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E),
      (LinearMap.adjoint : (F →ₗ[𝕜] E) → E →ₗ[𝕜] F) X.toLinearMap ∘ₗ TauCeti.ritzResidual A X = 0)
    (h_TauCeti_DavisKahan_FiniteDimensional_singularValues_sinThetaEmbedding_lt_one_of_isTransverse : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      (U : Submodule 𝕜 E) [inst_7 : U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E),
      TauCeti.IsTransverse (TauCeti.approximateSubspace X) U →
        ∀ (i : Fin (Module.finrank 𝕜 F)),
          ((TauCeti.sinThetaEmbedding U X).singularValues : ℕ → ℝ) (↑i : ℕ) < 1)
    (h_TauCeti_DavisKahan_FiniteDimensional_adjoint_apply_sinTheta_leftSingularVector : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      (U : Submodule 𝕜 E) [inst_7 : U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
      {i : Fin (Module.finrank 𝕜 F)},
      ((TauCeti.sinThetaEmbedding U X).singularValues : ℕ → ℝ) (↑i : ℕ) ≠ 0 →
        ((LinearMap.adjoint : (F →ₗ[𝕜] E) → E →ₗ[𝕜] F) X.toLinearMap : E → F)
            (TauCeti.leftSingularVector (TauCeti.sinThetaEmbedding U X) i) =
          (↑(((TauCeti.sinThetaEmbedding U X).singularValues : ℕ → ℝ) (↑i : ℕ)) : 𝕜) •
            (TauCeti.rightSingularBasis (TauCeti.sinThetaEmbedding U X) : Fin (Module.finrank 𝕜 F) → F)
              i)
    (h_TauCeti_adjoint_apply_leftSingularVector : ∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] [inst_4 : NormedAddCommGroup F]
      [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F)
      {i : Fin (Module.finrank 𝕜 E)},
      (A.singularValues : ℕ → ℝ) (↑i : ℕ) ≠ 0 →
        ((LinearMap.adjoint : (E →ₗ[𝕜] F) → F →ₗ[𝕜] E) A : F → E) (TauCeti.leftSingularVector A i) =
          (↑((A.singularValues : ℕ → ℝ) (↑i : ℕ)) : 𝕜) •
            (TauCeti.rightSingularBasis A : Fin (Module.finrank 𝕜 E) → E) i)
    (h_TauCeti_isInvariant_orthogonal_of_isSymmetric : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] {A : E →ₗ[𝕜] E},
      A.IsSymmetric → ∀ {U : Submodule 𝕜 E}, TauCeti.IsInvariant A U → TauCeti.IsInvariant A Uᗮ)
    :
    δ * tanTheta0.singularValues i ≤
      RCLike.re ⟪tanThetaResidualWitness U X i,
        ritzResidual A X (rightSingularBasis (sinThetaEmbedding U X) i)⟫_𝕜 := by
  let S := sinThetaEmbedding U X
  let M := compression A X
  let R := ritzResidual A X
  let σ := S.singularValues i
  let v := rightSingularBasis S i
  have hvnorm : ‖v‖ = 1 := (rightSingularBasis S).orthonormal.norm_eq_one i
  have hσnonneg : 0 ≤ σ := S.singularValues_nonneg i
  have htrans := h_TauCeti_DavisKahan_FiniteDimensional_isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap
  have hσlt : σ < 1 := h_TauCeti_DavisKahan_FiniteDimensional_singularValues_sinThetaEmbedding_lt_one_of_isTransverse U X htrans i
  have hcpos : 0 < Real.sqrt (1 - σ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have htan_i : tanTheta0.singularValues i = σ / Real.sqrt (1 - σ ^ 2) := by
    calc
      tanTheta0.singularValues i = principalTangents (approximateSubspace X) U i :=
        congrArg (fun z : ℕ →₀ ℝ => z (i : ℕ)) htan
      _ = Real.tan (Real.arcsin σ) := by
        simpa [S, σ] using h_TauCeti_DavisKahan_FiniteDimensional_principalTangents_approximateSubspace_apply U X (i : ℕ)
      _ = σ / Real.sqrt (1 - σ ^ 2) := Real.tan_arcsin σ
  by_cases hσzero : σ = 0
  · have hgal := LinearMap.congr_fun (h_TauCeti_adjoint_comp_ritzResidual_eq_zero A X) v
    change X.toLinearMap.adjoint (R v) = 0 at hgal
    have horth : ⟪X.toLinearMap v, R v⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_right, hgal, inner_zero_right]
    have hwitness : tanThetaResidualWitness U X i = X.toLinearMap v := by
      simp [tanThetaResidualWitness, S, σ, v, hσzero]
    rw [htan_i, hσzero, zero_div, mul_zero, hwitness]
    change 0 ≤ RCLike.re ⟪X.toLinearMap v, R v⟫_𝕜
    rw [horth]
    simp
  · let y := leftSingularVector S i
    have hynorm : ‖y‖ = 1 := by
      simpa [y] using (h_TauCeti_orthonormal_leftSingularVector_subtype S).norm_eq_one ⟨i, hσzero⟩
    have hSv : S v = ((σ : ℝ) : 𝕜) • y := by
      simpa [S, σ, v, y] using h_TauCeti_apply_rightSingularBasis_eq_smul_leftSingularVector S i
    have hSadj : S.adjoint y = ((σ : ℝ) : 𝕜) • v := by
      simpa [S, σ, v, y] using h_TauCeti_adjoint_apply_leftSingularVector S hσzero
    have hyUperp : y ∈ Uᗮ := by
      dsimp [y]
      rw [leftSingularVector]
      exact Uᗮ.smul_mem _ (Uᗮ.starProjection_apply_mem (X v))
    have hXadj : X.toLinearMap.adjoint y = ((σ : ℝ) : 𝕜) • v := by
      simpa [S, σ, v, y] using
        h_TauCeti_DavisKahan_FiniteDimensional_adjoint_apply_sinTheta_leftSingularVector U X hσzero
    have hMupper : RCLike.re ⟪M v, v⟫_𝕜 ≤ α := by
      have hTopRed : IsInvariant M ⊤ := fun z _ => Submodule.mem_top
      have hspec : PointSpectrumIn M ⊤ (Set.Iic α) := by
        intro lam hlam
        exact (hgap.1 hlam).2
      have hbound : RCLike.re ⟪M v, v⟫_𝕜 ≤ α * ‖v‖ ^ 2 :=
        h_TauCeti_upperFormBound_of_pointSpectrumIn (h_TauCeti_isSymmetric_compression hA X)
          hTopRed hspec v Submodule.mem_top
      simpa [hvnorm] using hbound
    have hAlower : α + δ ≤ RCLike.re ⟪A y, y⟫_𝕜 := by
      have hUperpRed : IsInvariant A Uᗮ := h_TauCeti_isInvariant_orthogonal_of_isSymmetric hA hU
      have hbound : (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
        h_TauCeti_lowerFormBound_of_pointSpectrumIn hA hUperpRed hgap.2 y hyUperp
      simpa [hynorm] using hbound
    have hSyl := LinearMap.congr_fun
      (h_TauCeti_sylvester_sinThetaEmbedding_eq_projectedResidual hA hU X M) v
    have hpair :
        RCLike.re ⟪y, R v⟫_𝕜 =
          σ * (RCLike.re ⟪A y, y⟫_𝕜 - RCLike.re ⟪M v, v⟫_𝕜) := by
      have hright :
          ⟪y, complementaryProjection U (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜 := by
        change ⟪y, Uᗮ.starProjection (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜
        rw [← Uᗮ.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hyUperp]
      have hsyl' : A (S v) - S (M v) = complementaryProjection U (R v) := by
        simpa [S, M, R, ritzResidual] using hSyl
      have hSM : ⟪y, S (M v)⟫_𝕜 = ⟪S.adjoint y, M v⟫_𝕜 := by
        exact (LinearMap.adjoint_inner_left S (M v) y).symm
      have hpairComplex :
          ⟪y, R v⟫_𝕜 =
            (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by
        calc
          ⟪y, R v⟫_𝕜 = ⟪y, complementaryProjection U (R v)⟫_𝕜 := hright.symm
          _ = ⟪y, A (S v) - S (M v)⟫_𝕜 := by rw [hsyl']
          _ = ⟪y, A (S v)⟫_𝕜 - ⟪y, S (M v)⟫_𝕜 := inner_sub_right _ _ _
          _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) - ⟪y, S (M v)⟫_𝕜 := by
            rw [hSv, map_smul, inner_smul_right]
          _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) -
              (((σ : ℝ) : 𝕜) * ⟪v, M v⟫_𝕜) := by
            rw [hSM, hSadj, inner_smul_left, RCLike.conj_ofReal]
          _ = (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by ring
      have hAy : RCLike.re ⟪y, A y⟫_𝕜 = RCLike.re ⟪A y, y⟫_𝕜 := by
        rw [← inner_conj_symm, RCLike.conj_re]
      have hMv : RCLike.re ⟪v, M v⟫_𝕜 = RCLike.re ⟪M v, v⟫_𝕜 := by
        rw [← inner_conj_symm, RCLike.conj_re]
      rw [hpairComplex, RCLike.re_ofReal_mul, map_sub, hAy, hMv]
    have hpair_lower : δ * σ ≤ RCLike.re ⟪y, R v⟫_𝕜 := by
      rw [hpair]
      nlinarith
    have hgal := LinearMap.congr_fun (h_TauCeti_adjoint_comp_ritzResidual_eq_zero A X) v
    change X.toLinearMap.adjoint (R v) = 0 at hgal
    have hXorth : ⟪X.toLinearMap v, R v⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_right, hgal, inner_zero_right]
    have hrawComplex :
        ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 =
          ⟪y, R v⟫_𝕜 := by
      rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, hXorth,
        mul_zero, sub_zero]
    have hraw :
        RCLike.re ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 =
          RCLike.re ⟪y, R v⟫_𝕜 := congrArg RCLike.re hrawComplex
    let c := Real.sqrt (1 - σ ^ 2)
    have hcpos' : 0 < c := by simpa [c] using hcpos
    have hscale :
        RCLike.re ⟪((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)), R v⟫_𝕜 =
          RCLike.re ⟪y, R v⟫_𝕜 / c := by
      calc
        RCLike.re ⟪((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)), R v⟫_𝕜 =
            c⁻¹ * RCLike.re
              ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 := by
                rw [inner_smul_left, map_inv₀, RCLike.conj_ofReal,
                  ← RCLike.ofReal_inv, RCLike.re_ofReal_mul]
        _ = c⁻¹ * RCLike.re ⟪y, R v⟫_𝕜 := by rw [hraw]
        _ = RCLike.re ⟪y, R v⟫_𝕜 / c := by
          simp [div_eq_mul_inv, mul_comm]
    rw [htan_i]
    change δ * (σ / c) ≤
      RCLike.re ⟪
        (if σ = 0 then X.toLinearMap v else
          ((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v))),
        R v⟫_𝕜
    rw [ite_eq_right hσzero, hscale]
    simpa [div_eq_mul_inv, mul_assoc] using
      (div_le_div_iff_of_pos_right hcpos').2 hpair_lower

end DavisKahan.FiniteDimensional
end TauCeti
