/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Examples.SauersML__group_approximation.Dependencies.v4cc78e7ce361.GroupApproximation.Toeplitz.FockModule
set_option warningAsError true
/-!
# Sums of products of two creation operators

Let `M` be a submodule of sections of the Fock space that is invariant under the creation operators
of a set `E` of sections and under the annihilation operators of the sections that are continuous
against `E` (`IsFockInvariant`).  For finitely many admissible sections `u k`, `v k`, the operator
`creationPairs u v = ∑_k ℓ(u k) ℓ(v k)` has the adjoint `annihilationPairs u v = ∑_k ℓ(v k)* ℓ(u k)*`
(`isSectionAdjoint_creationPairs`), and

`annihilationPairs u' v' * creationPairs u v = (∑_{i,j} ⟪u' i, u j⟫ ⟪v' i, v j⟫) • 1`

at every point (`annihilationPairs_mul_creationPairs_apply`).  So when the scalar sums are `1`, `0`
and `1`, the operators `creationPairs u v₁` and `creationPairs u v₂` are isometries with orthogonal
ranges (`exists_properlyInfinite_of_coeff`), and they lie in every set of operators with the closure
properties of a Toeplitz algebra (`IsToeplitzClosed`).
-/
namespace GroupApproximation.Toeplitz
noncomputable section
open scoped ENNReal InnerProductSpace
variable {X : Type*} {ι : Type*} {κ : Type*}
/-- `M` is invariant under the creation operators of `E` and under the annihilation operators of
the sections whose pointwise inner products with `E` are continuous. -/
structure IsFockInvariant [TopologicalSpace X] (E : Set (Sections X (Fib ι)))
    (M : Submodule ℂ (Sections X (Fock ι))) : Prop where
  creation : ∀ ζ ∈ E, ∀ ω ∈ M, creationSec ζ ω ∈ M
  annihilation : ∀ ζ : Sections X (Fib ι), (∀ ζ' ∈ E, Continuous fun x => ⟪ζ x, ζ' x⟫_ℂ) →
    ∀ ω ∈ M, annihilationSec ζ ω ∈ M
/-- A section of `E` whose pointwise inner products with the sections of `E` are continuous. -/
def IsAdmissible [TopologicalSpace X] (E : Set (Sections X (Fib ι))) (ζ : Sections X (Fib ι)) :
    Prop :=
  ζ ∈ E ∧ ∀ ζ' ∈ E, Continuous fun x => ⟪ζ x, ζ' x⟫_ℂ
/-- The closure properties of a Toeplitz algebra: `1`, the creation operators of `E`, sums, scalar
multiples, products and adjoints. -/
structure IsToeplitzClosed (E : Set (Sections X (Fib ι))) {M : Submodule ℂ (Sections X (Fock ι))}
    (𝒯 : Set (Module.End ℂ M)) : Prop where
  one_mem : 1 ∈ 𝒯
  creation_mem : ∀ ζ ∈ E, ∀ T : Module.End ℂ M, (∀ (ω : M) (x : X) (w : List ι),
    (((T ω : M) : Sections X (Fock ι)) x : List ι → ℂ) w =
      tensorCoord (ζ x : ι → ℂ) ((ω : Sections X (Fock ι)) x : List ι → ℂ) w) → T ∈ 𝒯
  add_mem : ∀ S ∈ 𝒯, ∀ T ∈ 𝒯, S + T ∈ 𝒯
  smul_mem : ∀ c : ℂ, ∀ T ∈ 𝒯, c • T ∈ 𝒯
  mul_mem : ∀ S ∈ 𝒯, ∀ T ∈ 𝒯, S * T ∈ 𝒯
  adjoint_mem : ∀ T ∈ 𝒯, ∀ S, IsSectionAdjoint T S → S ∈ 𝒯
end
end GroupApproximation.Toeplitz
