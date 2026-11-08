module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/shared/Shared/Algebraic/BilinearForm/Basic.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Defs
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
/-!
# Bilinear forms — algebraic core (field-generic)

Field-generic, fully computable core for symmetric positive-definite
bilinear forms: `B : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜` with computable `inner`,
`IsSymm`, `IsPosDef` predicates. Avoids continuous linear maps,
smoothness, and any non-computable Mathlib infrastructure.

Specialises to Riemannian metrics when `𝕜 = ℝ` + smoothness; the
algebraic operations evaluate to actual numbers on a computable field
like `ℚ`. Also reusable for Hermitian forms (`𝕜 = ℂ`), quadratic forms,
positive-definite forms in optimisation, matrix calculus.
-/
namespace BilinearForm
/-- A bilinear form on `V` over `𝕜`: a linear map
`V →ₗ[𝕜] V →ₗ[𝕜] 𝕜`. Definitionally Mathlib's `LinearMap.BilinForm`. -/
abbrev Form (𝕜 : Type*) [CommSemiring 𝕜]
    (V : Type*) [AddCommMonoid V] [Module 𝕜 V] :=
  LinearMap.BilinForm 𝕜 V
section Algebra
variable {𝕜 : Type*} [Field 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]
def inner (B : Form 𝕜 V) (v w : V) : 𝕜 :=
  B v w
end Algebra
section Order
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]
end Order
end BilinearForm
