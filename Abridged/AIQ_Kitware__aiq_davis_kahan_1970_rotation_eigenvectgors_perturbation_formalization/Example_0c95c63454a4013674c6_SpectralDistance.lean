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
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
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
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.LinearAlgebra.Lagrange

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vbe02f784e39d.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated false
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

/-- The finite-dimensional point spectrum of `A` carried by `U`.

For symmetric operators this is the spectrum of the restriction to `U` once
`U` reduces `A`.  The definition avoids exposing a choice of restricted
coordinate space in theorem statements.

Eigenvectors are Mathlib's `Module.End.HasEigenvector` rather than a local predicate; the
only thing a local one added was to fix the eigenvalue as real, which is a property of the
`lam : ℝ` binder here and not of the notion of eigenvector. -/
def restrictedPointSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ Module.End.HasEigenvector A (lam : 𝕜) x}

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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vbe02f784e39d.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Finite-dimensional spectral-gap predicates

Canonical separation hypotheses used by the sine, tangent, double-angle, and
Sylvester theorem families.

## Sources

The spectral-gap predicates are the hypotheses of Davis--Kahan's `sin Θ` theorem in
the form the theorem consumes; see
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Core/SpectralGap.lean`
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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Two restricted spectra are separated by at least `δ`. -/
@[expose]
def PointSpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedPointSpectrum A U → μ ∈ restrictedPointSpectrum B V →
    δ ≤ |lam - μ|

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vbe02f784e39d.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Internal finite-dimensional spectral bounds for Sylvester estimates

Eigenvalue-to-quadratic-form conversions and centered spectral bounds shared by
the interval and arbitrary-distance Sylvester arguments. These declarations are
implementation support rather than part of the public theorem surface.

## Sources

*Follows nothing in particular*: internal bounds extracted from the Sylvester estimate's
proof, kept separate so the main file states only the estimate.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Sylvester/Internal/SpectralBounds.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/
public section
namespace TauCeti
open TauCeti
open scoped InnerProductSpace BigOperators
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
set_option linter.unusedVariables false in
axiom _root_.TauCeti.eigenvalue_mem_restrictedPointSpectrum_top.{w_u_1,w_u_2} : ∀ {𝕜 : Type w_u_1} [inst : RCLike 𝕜] {E : Type w_u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
  (hT : T.IsSymmetric) (i : Fin (Module.finrank 𝕜 E)),
  hT.eigenvalues rfl i ∈ TauCeti.restrictedPointSpectrum T ⊤

end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vbe02f784e39d.ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SingularSubspace.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

Groundwork for the Yu–Wang–Samworth singular-vector extension: perturbing the
Gram operator `A⋆A` by `Â⋆Â − A⋆A`, controlled by `Â − A`.  Includes the operator
adjoint norm bound `‖A⋆‖ = ‖A‖` in elementwise form.

Plan step W0.1(d) added by Claude Opus 4.8 (claude-opus-4-8[1m]): the
singular-value symmetry `σ(A⋆) = σ(A)` for a square operator, proved through the
eigenvalue invariance of a symmetric operator under unitary conjugation
(`eigenvalues_conj_unitary`, a Courant–Fischer consequence) applied to the polar
identity `A A⋆ = U (A⋆A) U⁻¹` with `U = choosePolarUnitary A`.
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-! # Gram-operator perturbation

For `A, Â : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
singular subspaces are the spectral subspaces of the Gram operators `A⋆A` and
`Â⋆Â`.  The Yu–Wang–Samworth singular-vector bound applies the symmetric result
to these Gram operators, so it needs the Gram perturbation `Â⋆Â − A⋆A` bounded in
terms of `Â − A`.

## Main results

* `TauCeti.norm_adjoint_apply_le`: the adjoint of a `c`-bounded operator is
  `c`-bounded (`‖A⋆‖ ≤ ‖A‖` in elementwise form).
* `TauCeti.norm_gram_sub_gram_apply_le`: `‖(Â⋆Â − A⋆A) x‖ ≤ (a + â) ε ‖x‖`
  when `A, Â, Â − A` are `a`-, `â`-, `ε`-bounded, via
  `Â⋆Â − A⋆A = Â⋆(Â − A) + (Â − A)⋆A`.
* `TauCeti.abs_sq_singularValues_sub_le`: Weyl for squared singular values,
  `|σₖ(Â)² − σₖ(A)²| ≤ (a + â) ε` — the singular-value stability underlying the
  singular-subspace bound.
* `TauCeti.sum_sq_singularValues`: the squared Frobenius norm equals the sum
  of squared singular values, `∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²`.
* `TauCeti.eigenvalues_conj_unitary`: the sorted eigenvalues of a symmetric
  operator are invariant under unitary conjugation `S ↦ U S U⁻¹`.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), §"singular-vector extension".
-/
public section
namespace TauCeti
open scoped InnerProductSpace
open LinearMap
open Module (finrank)
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

set_option linter.unusedVariables false in
axiom _root_.TauCeti.sum_sq_norm_apply_unitary_comp.{w_u_1,w_u_2,w_u_3} : ∀ {𝕜 : Type w_u_1} {E : Type w_u_2} {F : Type w_u_3} [inst : RCLike 𝕜]
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (A : E →ₗ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E) {n : ℕ},
  Module.finrank 𝕜 E = n →
    ∀ (b : OrthonormalBasis (Fin n) 𝕜 E),
      ∑ k : Fin n, ‖(A : E → F) ((U : E → E) ((b : Fin n → E) k))‖ ^ 2 =
        ∑ k : Fin n, ‖(A : E → F) ((b : Fin n → E) k)‖ ^ 2

/-! ### Extreme singular values: variational characterization

The largest singular value is the operator norm and the smallest is the
minimum gain, both attained.  These are the quantitative
inputs for the operator-norm principal-angle identification. -/
section Extreme
variable {n : ℕ}

end Extreme
/-! ### Singular values of the adjoint (square case)

`σ(A⋆) = σ(A)` for a square operator `A : E →ₗ[𝕜] E`.  The Gram operators
`A⋆A` and `A A⋆` are unitarily conjugate (`A A⋆ = U (A⋆A) U⁻¹` with
`U = choosePolarUnitary A`), so they have equal sorted eigenvalues, hence `A` and
`A⋆` have equal singular values.  This is the symmetry `cosPrincipalAngles`
needs (plan step W0.1(d)).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SingularSubspace`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `29506b0`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/
section Adjoint
variable {n : ℕ}

end Adjoint
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vbe02f784e39d.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Unitarily invariant seminorms on rectangular linear maps

The structure extends `Seminorm` and adds invariance under independent unitary actions on
its domain and codomain. This module supplies its function and seminorm instances,
finite two-sided orbit certificates, singular-value invariance, and isometric transport.

## Provenance

Adapted from the square and rectangular unitarily invariant seminorm modules in the
Davis--Kahan/DKPS formalization (Kitware, Inc.). The finite orbit and isometric-transport
proofs were originally part of the rectangular module.
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
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]
/-- A seminorm on rectangular linear maps, invariant under independent unitary
changes of domain and codomain coordinates. Square operators use `E = F`. -/
structure UnitarilyInvariantSeminorm (𝕜 E F : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] extends Seminorm 𝕜 (E →ₗ[𝕜] F) where
  /-- Two-sided unitary invariance. The left unitary acts on the codomain. -/
  unitary_invariant' :
    ∀ (U : unitary (F →ₗ[𝕜] F))
      (V : unitary (E →ₗ[𝕜] E)) A,
      toFun ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ
        (V : E →ₗ[𝕜] E)) = toFun A
namespace UnitarilyInvariantSeminorm
/-- A unitarily invariant seminorm is a function on rectangular maps, injectively so:
the seminorm laws and the invariance field are propositions. -/
instance : FunLike (UnitarilyInvariantSeminorm 𝕜 E F) (E →ₗ[𝕜] F) ℝ where
  coe N := N.toFun
  coe_injective := by
    rintro ⟨N, _hN⟩ ⟨M, _hM⟩ h
    have hNM : N = M := Seminorm.ext (fun A => congrFun h A)
    cases hNM
    rfl

set_option linter.unusedVariables false in
axiom _root_.TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry.{w_u_1,w_u_2,w_u_3} : ∀ {𝕜 : Type w_u_1} [inst : RCLike 𝕜] {E : Type w_u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type w_u_3}
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
  {f : (E →ₗ[𝕜] F) → ℝ},
  (∀ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F),
      f ((↑U.toLinearEquiv : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (↑V.toLinearEquiv : E →ₗ[𝕜] E)) = f A) →
    ∀ (U : ↥(unitary (F →ₗ[𝕜] F))) (V : ↥(unitary (E →ₗ[𝕜] E))) (A : E →ₗ[𝕜] F),
      f ((↑U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (↑V : E →ₗ[𝕜] E)) = f A
variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

end UnitarilyInvariantSeminorm
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vbe02f784e39d.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Instances ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Standard unitarily invariant seminorms

The operator norm, Frobenius norm, Ky Fan seminorms and nuclear norm are instances of the
same rectangular structure. Adjoint transport reverses the domain and codomain.
Frobenius evaluation is independent of the orthonormal basis of the domain.

Ky Fan dominance is equivalent to comparison in every seminorm of this structure.
The singular-value variational principles used to construct these instances live in
`ForTauCeti.Analysis.InnerProductSpace.KyFan`, without a norm-structure dependency.

## Provenance

Adapted from the square and rectangular norm-instance modules in the Davis--Kahan/DKPS
formalization (Kitware, Inc.).
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
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]
namespace UnitarilyInvariantSeminorm
variable (N : UnitarilyInvariantSeminorm 𝕜 E F)
/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/

/-- Operator norm as a rectangular UI norm. -/
@[expose]
noncomputable def opNorm : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := Seminorm.of
    (fun A => ‖A.toContinuousLinearMap‖)
    (fun A B => by
      rw [map_add]
      exact norm_add_le _ _)
    (fun a A => by
      rw [map_smul]
      exact norm_smul a _)
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (f := fun A : E →ₗ[𝕜] F => ‖A.toContinuousLinearMap‖)
      (fun U V A => by
        have hcomp :
            (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
              (U : F →L[𝕜] F) ∘L A.toContinuousLinearMap ∘L (V : E →L[𝕜] E) := by
          ext x
          simp
        change ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap‖
            = ‖A.toContinuousLinearMap‖
        rw [hcomp]
        simp)

set_option linter.unusedVariables false in
axiom _root_.TauCeti.UnitarilyInvariantSeminorm.sqrt_sum_add_sq_le : ∀ {m : ℕ} (f g : Fin m → ℝ),
  √(∑ i : Fin m, (f i + g i) ^ 2) ≤ √(∑ i : Fin m, f i ^ 2) + √(∑ i : Fin m, g i ^ 2)
/-- Frobenius/Hilbert--Schmidt norm as a rectangular UI norm. -/
@[expose]
noncomputable def frobenius : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := Seminorm.of
    (fun A => Real.sqrt
      (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2))
    (fun A B => by
      have hmono :
          Real.sqrt (∑ i, ‖(A + B) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) ≤
            Real.sqrt (∑ i, (‖A (stdOrthonormalBasis 𝕜 E i)‖ +
              ‖B (stdOrthonormalBasis 𝕜 E i)‖) ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [LinearMap.add_apply]
        exact norm_add_le _ _
      exact hmono.trans (UnitarilyInvariantSeminorm.sqrt_sum_add_sq_le _ _))
    (fun a A => by
      have h : ∀ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
          ‖a‖ ^ 2 * ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := fun i => by
        rw [LinearMap.smul_apply, norm_smul, mul_pow]
      rw [show (∑ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
          ‖a‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => h i,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)])
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (f := fun A : E →ₗ[𝕜] F => Real.sqrt
        (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2))
      (fun U V A => by
        change Real.sqrt (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
              (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
            = Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        have key : ∀ i,
            ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
                (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
              ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 := fun i => by
          rw [show (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
              (stdOrthonormalBasis 𝕜 E i) =
              U (A (V (stdOrthonormalBasis 𝕜 E i))) from rfl,
            U.norm_map]
        rw [show (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
              (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
            ∑ i, ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 from
            Finset.sum_congr rfl fun i _ => key i,
          sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)])

end UnitarilyInvariantSeminorm
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_0c95c63454a4013674c6_SpectralDistance ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Sylvester estimates for arbitrary separated spectra

The reciprocal spectral multiplier, finite orbit certificates, and the sharp
`pi / 2` Ky Fan and arbitrary-UI-norm bounds over real and complex scalars.

## Provenance

Originally developed in `DavisKahan/FiniteDimensional/Sylvester/SpectralDistance.lean`.
The reciprocal-multiplier estimate and rectangular Fan dominance are shared by
all scalar fields covered by `RCLike`.

-/
public section
namespace TauCeti
open scoped InnerProductSpace BigOperators
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-! ## Arbitrary disjoint spectra

The Bhatia--Davis--McIntosh extension is factored through the simultaneous Ky
Fan prefix estimate and rectangular Fan dominance.
-/

/-! ## Arbitrary disjoint spectra: the sharp Hilbert--Schmidt estimate

The `π/2` loss above is unavoidable for a general unitarily invariant norm, but
the Frobenius norm loses nothing under arbitrary positive separation.  The
coordinate equation `(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ` divides entrywise, and Parseval in the
two eigenbases sums the squares.  This is the estimate behind the
Hilbert--Schmidt form of Davis--Kahan Theorem 6.2.
-/
set_option linter.unusedVariables false in
/-- **Frobenius Sylvester estimate, constant one.**  Under arbitrary positive
spectral separation the Hilbert--Schmidt norm of a Sylvester solution is
controlled by the residual with no dimensional or analytic loss. -/
theorem frobenius_sylvester_le_of_pointSpectraSeparated
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) 
    (h_TauCeti_sylvester_eigenbasis_coefficient_equation : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F} (hA : A.IsSymmetric) (hB : B.IsSymmetric),
      A ∘ₗ X - X ∘ₗ B = C →
        ∀ (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)),
          ((↑(hA.eigenvalues rfl i) : 𝕜) - (↑(hB.eigenvalues rfl j) : 𝕜)) *
              Inner.inner 𝕜 ((X : E → F) ((hB.eigenvectorBasis rfl : Fin (Module.finrank 𝕜 E) → E) j))
                ((hA.eigenvectorBasis rfl : Fin (Module.finrank 𝕜 F) → F) i) =
            Inner.inner 𝕜 ((C : E → F) ((hB.eigenvectorBasis rfl : Fin (Module.finrank 𝕜 E) → E) j))
              ((hA.eigenvectorBasis rfl : Fin (Module.finrank 𝕜 F) → F) i))
    (h_TauCeti_UnitarilyInvariantSeminorm_frobenius_apply_basis : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      {n : ℕ} (A : E →ₗ[𝕜] F),
      Module.finrank 𝕜 E = n →
        ∀ (b : OrthonormalBasis (Fin n) 𝕜 E),
          (TauCeti.UnitarilyInvariantSeminorm.frobenius : (E →ₗ[𝕜] F) → ℝ) A =
            √(∑ i : Fin n, ‖(A : E → F) ((b : Fin n → E) i)‖ ^ 2))
    :
    δ * UnitarilyInvariantSeminorm.frobenius X ≤
      UnitarilyInvariantSeminorm.frobenius C := by
  classical
  set bA := hA.eigenvectorBasis rfl with hbA
  set bB := hB.eigenvectorBasis rfl with hbB
  -- the coordinate equation divides by a denominator of size at least `δ`
  have hentry : ∀ (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)),
      δ * ‖⟪X (bB j), bA i⟫_𝕜‖ ≤ ‖⟪C (bB j), bA i⟫_𝕜‖ := by
    intro i j
    have hcoef := h_TauCeti_sylvester_eigenbasis_coefficient_equation hA hB hEq i j
    have hsep : δ ≤ |hA.eigenvalues rfl i - hB.eigenvalues rfl j| :=
      hgap _ _ (eigenvalue_mem_restrictedPointSpectrum_top hA i)
        (eigenvalue_mem_restrictedPointSpectrum_top hB j)
    have hnorm :
        ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))‖ =
          |hA.eigenvalues rfl i - hB.eigenvalues rfl j| := by
      rw [show ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) =
        ((hA.eigenvalues rfl i - hB.eigenvalues rfl j : ℝ) : 𝕜) by push_cast; ring]
      exact RCLike.norm_ofReal _
    calc
      δ * ‖⟪X (bB j), bA i⟫_𝕜‖
          ≤ |hA.eigenvalues rfl i - hB.eigenvalues rfl j| *
              ‖⟪X (bB j), bA i⟫_𝕜‖ := by
            gcongr
      _ = ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))‖ *
              ‖⟪X (bB j), bA i⟫_𝕜‖ := by rw [hnorm]
      _ = ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
              ⟪X (bB j), bA i⟫_𝕜‖ := (norm_mul _ _).symm
      _ = ‖⟪C (bB j), bA i⟫_𝕜‖ := by rw [hcoef]
  -- Parseval in the codomain eigenbasis turns the entry bound into a column bound
  have hcol : ∀ j : Fin (Module.finrank 𝕜 E),
      δ ^ 2 * ‖X (bB j)‖ ^ 2 ≤ ‖C (bB j)‖ ^ 2 := by
    intro j
    rw [← bA.sum_sq_norm_inner_left (X (bB j)),
      ← bA.sum_sq_norm_inner_left (C (bB j)), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc
      δ ^ 2 * ‖⟪X (bB j), bA i⟫_𝕜‖ ^ 2
          = (δ * ‖⟪X (bB j), bA i⟫_𝕜‖) ^ 2 := by ring
      _ ≤ ‖⟪C (bB j), bA i⟫_𝕜‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hentry i j) 2
  have htot : δ ^ 2 * (∑ j, ‖X (bB j)‖ ^ 2) ≤ ∑ j, ‖C (bB j)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcol j
  rw [h_TauCeti_UnitarilyInvariantSeminorm_frobenius_apply_basis X rfl bB,
    h_TauCeti_UnitarilyInvariantSeminorm_frobenius_apply_basis C rfl bB,
    ← Real.sqrt_sq hδ.le, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt htot
end TauCeti
