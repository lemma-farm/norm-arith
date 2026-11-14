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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap ====
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.KyFan ====
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
set_option linter.deprecated false
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

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic ====
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

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

set_option linter.unusedVariables false in
axiom _root_.TauCeti.UnitarilyInvariantSeminorm.smul_eq.{w_u_1,w_u_2,w_u_3} : ∀ {𝕜 : Type w_u_1} [inst : RCLike 𝕜] {E : Type w_u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type w_u_3}
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
  (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E F) (a : 𝕜) (A : E →ₗ[𝕜] F),
  (N : (E →ₗ[𝕜] F) → ℝ) (a • A) = ‖a‖ * (N : (E →ₗ[𝕜] F) → ℝ) A

end UnitarilyInvariantSeminorm
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Majorization ====
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
# Ky Fan majorization for rectangular unitarily invariant norms

The engine of the theory: a map whose Ky Fan sums are dominated by another's lies in
the convex hull of the latter's two-sided unitary orbit, and therefore has the smaller
value under *every* rectangular unitarily invariant norm.

The majorization step itself is not proved here.  The two-sided unitary orbit's convex hull
pulls back along a diagonal lift to a `FiniteVector.IsSymmetricConvex` set of coordinate
vectors — coordinate swaps and single-coordinate sign changes are two-sided unitary actions —
so the Hardy--Littlewood--Pólya transfer descent
`FiniteVector.IsSymmetricConvex.mem_of_prefixSum_le` applies directly.  What remains here is
the operator-theoretic half: the lift, the extension of coordinate unitaries to the ambient
spaces, and the transport of equal singular-value data by the rectangular SVD.

## Provenance

Adapted from the rectangular majorization and block-sum modules in the Davis--Kahan/DKPS
formalization (Kitware, Inc.). The vector majorization descent remains in
`ForTauCeti.Analysis.Convex.Majorization`.
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

set_option linter.unusedVariables false in
axiom _root_.TauCeti.UnitarilyInvariantSeminorm.apply_le_of_kyFanSum_le.{w_u_1,w_u_2,w_u_3} : ∀ {𝕜 : Type w_u_1} [inst : RCLike 𝕜] {E : Type w_u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type w_u_3}
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
  (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E F) {A B : E →ₗ[𝕜] F},
  (∀ (k : ℕ), TauCeti.kyFanSum k A ≤ TauCeti.kyFanSum k B) →
    (N : (E →ₗ[𝕜] F) → ℝ) A ≤ (N : (E →ₗ[𝕜] F) → ℝ) B
/-! ### The operator-ideal property -/

end UnitarilyInvariantSeminorm
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_ff0c93a0a39ef834e897_SpectralDistance ====
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


set_option linter.unusedVariables false in
/-- General disjoint-spectrum extension with the Bhatia--Davis--McIntosh
constant `π/2`, obtained from Ky Fan prefixes by rectangular Fan dominance.
-/
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) 
    (h_TauCeti_kyFanSum_real_smul : ∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] [inst_4 : NormedAddCommGroup F]
      [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F] (k : ℕ) (A : E →ₗ[𝕜] F) {r : ℝ},
      0 ≤ r → TauCeti.kyFanSum k ((↑r : 𝕜) • A) = r * TauCeti.kyFanSum k A)
    (h_TauCeti_kyFan_sylvester_le_of_spectralDistance : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
      [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
      {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F},
      A.IsSymmetric →
        B.IsSymmetric →
          ∀ {δ : ℝ},
            0 < δ →
              TauCeti.PointSpectraSeparated A ⊤ B ⊤ δ →
                A ∘ₗ X - X ∘ₗ B = C →
                  ∀ (k : ℕ), δ * TauCeti.kyFanSum k X ≤ Real.pi / 2 * TauCeti.kyFanSum k C)
    :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : 𝕜)) • X) ≤ N (((p : 𝕜)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    rw [h_TauCeti_kyFanSum_real_smul k X hδ0,
      h_TauCeti_kyFanSum_real_smul k C hp0]
    simpa [p] using
      h_TauCeti_kyFan_sylvester_le_of_spectralDistance hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : 𝕜)) • X) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos hδ]
    _ ≤ N (((p : 𝕜)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl
/-! ## Arbitrary disjoint spectra: the sharp Hilbert--Schmidt estimate

The `π/2` loss above is unavoidable for a general unitarily invariant norm, but
the Frobenius norm loses nothing under arbitrary positive separation.  The
coordinate equation `(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ` divides entrywise, and Parseval in the
two eigenbases sums the squares.  This is the estimate behind the
Hilbert--Schmidt form of Davis--Kahan Theorem 6.2.
-/
end TauCeti
