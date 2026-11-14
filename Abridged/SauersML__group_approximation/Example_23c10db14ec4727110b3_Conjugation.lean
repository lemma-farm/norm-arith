import Mathlib.Analysis.InnerProductSpace.PiL2

-- ==== Examples.SauersML__group_approximation.Examples.Example_23c10db14ec4727110b3_Conjugation ====
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Vendored from https://github.com/TauCetiProject/TauCeti, module `TauCeti.Analysis.InnerProductSpace.Conjugation`,
commit 2bd433b4598b84db4b8662305d2dd4927cf1c173 (2026-08-25), and adapted to this repository's
Lean/Mathlib pin: the `module` system header is removed and the `TauCeti.*`
imports are re-rooted under `GroupApproximation.External.TauCeti`; the
mathematics and the declaration names are unchanged.
-/
set_option warningAsError true
/-!
# Coordinatewise conjugation in an orthonormal basis

There is no canonical conjugation on an abstract inner product space, so this file attaches one to
an orthonormal basis `e` by conjugating the coordinates in it:
`conjugation e x = ∑ i, conj ⟪e i, x⟫ • e i`. It is a conjugate-linear isometric involution of `V`
(`TauCeti.conjugation_conjugation`, `TauCeti.inner_conjugation_conjugation`), and conjugating an
operator by it, `A ↦ J ∘ A ∘ J` (`TauCeti.conjCLM`), is the coordinate-free description of
conjugating the matrix of `A` entrywise.

## Main definitions

* `TauCeti.conjugation`: the conjugate-linear isometric involution attached to an orthonormal basis.
* `TauCeti.conjCLM`: conjugation of a continuous linear operator, `A ↦ J ∘ A ∘ J`.

## Main statements

* `TauCeti.conjugation_conjugation` and `TauCeti.inner_conjugation_conjugation`: conjugation is an
  involution, and reverses the inner product.
* `TauCeti.conjugation_basis`: the basis it is attached to is fixed vector by vector, which is what
  makes it *the* conjugation of that basis.
* `TauCeti.inner_conjugation_left_basis`: pairing a conjugate against a basis vector swaps the two
  arguments of the inner product.
* `TauCeti.conjCLM_one`, `TauCeti.conjCLM_mul` and `TauCeti.conjCLM_conjCLM`: conjugation of
  operators is a multiplicative involution fixing the identity.
* `TauCeti.conjCLM_add` and `TauCeti.conjCLM_smul`: it is additive and conjugate-linear, so with
  the two preceding it is a conjugate-linear ring involution of the operators.
* `TauCeti.norm_conjCLM`: conjugation of operators preserves the operator norm.
-/
open scoped InnerProductSpace
namespace TauCeti
section Conjugation
variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
/-- **Coordinatewise conjugation in an orthonormal basis.** A conjugate-linear isometric involution
of `V`, which on coordinates is `x i ↦ conj (x i)`. -/
noncomputable def conjugation (e : OrthonormalBasis ι 𝕜 V) (x : V) : V :=
  ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i
variable (e : OrthonormalBasis ι 𝕜 V)

/-- Conjugation is additive. -/
@[simp]
axiom conjugation_add (x y : V) :
    conjugation e (x + y) = conjugation e x + conjugation e y
/-- Conjugation is conjugate-linear: a scalar comes out conjugated. -/
@[simp]
axiom conjugation_smul (c : 𝕜) (x : V) :
    conjugation e (c • x) = (starRingEnd 𝕜) c • conjugation e x

/-- Conjugation is isometric, as the reversal of the inner product shows on the diagonal. -/
@[simp]
axiom norm_conjugation (x : V) : ‖conjugation e x‖ = ‖x‖
end Conjugation
section ConjugateOperator
variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)
/-- **Conjugation of a continuous linear operator**, `A ↦ J ∘ A ∘ J` for `J` the conjugation of `e`.
The two conjugate-linearities of `J` cancel, so the result is `𝕜`-linear, and it is bounded because
`J` is isometric. -/
noncomputable def conjCLM (A : V →L[𝕜] V) : V →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun x := conjugation e (A (conjugation e x))
      map_add' x y := by simp
      map_smul' c x := by simp } ‖A‖ fun x ↦ by
    simpa using A.le_opNorm (conjugation e x)

end ConjugateOperator
end TauCeti
