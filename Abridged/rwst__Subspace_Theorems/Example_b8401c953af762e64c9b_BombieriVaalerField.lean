module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Algebra.Module.LinearMap.Rat

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.va75ab00733d7.ArithmeticHeights.Arakelov ====
public section
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The Arakelov height over a number field

Mathlib's `Height.mulHeight` measures a tuple by the **sup norm** at every place. In Arakelov
theory one instead uses the **ℓ² norm at the archimedean places** — the Fubini–Study metric on
`O(1)` — and keeps the sup norm at the finite places. The resulting height is the one in which
the constants of the Siegel-lemma literature (Bombieri–Vaaler, Schmidt) are stated.

This file defines that normalization over a number field `K` and proves its basic API — scaling
invariance and the descent to projective space, `1 ≤ H_Ar`, invariance under reindexing, and the
affine case — together with the two-sided comparison with `Height.mulHeight`, which is what lets
a bound stated in either normalization be read in the other. Not all of
`Mathlib.NumberTheory.Height.Basic` transfers here — see the implementation notes.

## Main definitions

* `NumberField.arakelovMulHeight x` for `x : ι → K`: the multiplicative Arakelov height
  `∏_{v | ∞} (∑ i, v (x i)²)^{mult v / 2} · ∏ᶠ_{v ∤ ∞} ⨆ i, v (x i)`.
* `NumberField.arakelovLogHeight x`: its logarithm.
* `NumberField.arakelovMulHeight₁ x` and `NumberField.arakelovLogHeight₁ x` for `x : K`:
  the one-variable (affine) case, the height of the tuple `![x, 1]`.
* `Projectivization.arakelovMulHeight` and `Projectivization.arakelovLogHeight`: the descent
  of the above to `Projectivization K (ι → K)`, which the scaling invariance below justifies.

## Main results

* `NumberField.arakelovMulHeight_smul_eq`: invariance under scaling by a nonzero element of
  `K`, by the product formula. This is what makes the height projective.
* `NumberField.one_le_arakelovMulHeight`: the Arakelov height is at least `1`.
* `NumberField.arakelovMulHeight_comp_equiv`: invariance under reindexing.
* `NumberField.arakelovMulHeight_one` and `NumberField.arakelovMulHeight₁_one`: the values
  `#ι ^ (totalWeight K / 2)` and `2 ^ (totalWeight K / 2)` on the all-ones tuple and at `1`,
  where the sup-norm height is `1` — the two normalizations genuinely differ.
* `NumberField.arakelovLogHeight₁_eq`: the local formula for the affine logarithmic height,
  with `log⁺ (v x)` at the finite places.
* `NumberField.mulHeight_le_arakelovMulHeight` and `NumberField.arakelovMulHeight_le_mulHeight`:
  the two comparisons with Mathlib's sup-norm height, the second with the constant
  `#ι ^ (totalWeight K / 2)`. These are what transport a constant stated for one normalization
  into the other, and the second is sharp: it is an equality at the all-ones tuple.
* `NumberField.arakelovMulHeight₁_le_mulHeight₁`: the affine case of the same, with constant
  `2 ^ (totalWeight K / 2)` — there is no equality `arakelovMulHeight₁ = mulHeight₁`.
* `Projectivization.mulHeight_le_arakelovMulHeight` and
  `Projectivization.arakelovMulHeight_le_mulHeight`: the same two comparisons on projective space,
  where the heights of Layer 3 live. The first is what makes the Northcott property of Layer 1.1
  carry over to the Arakelov normalization, since it bounds the sup-norm height by the Arakelov
  one with no constant at all.

## Implementation notes

As for `Height.mulHeight`, the zero tuple gets the junk value `1`: the displayed product is `0`
there, which would break `1 ≤ arakelovMulHeight` and the comparison with `Height.mulHeight`.
`NumberField.arakelovMulHeight_eq` recovers the displayed formula for a nonzero tuple, and every
statement below holds unconditionally with this convention.

The index type carries `Fintype` rather than `Finite` because the archimedean local factor is a
`Finset.sum` over `ι`; the value does not depend on the instance.

Only the archimedean factor differs from `NumberField.mulHeight_eq`. Accordingly the proof of
scaling invariance does not redo the product-formula bookkeeping at the finite places: the
transformation law of the finite part is *extracted* from Mathlib's
`Height.mulHeight_smul_eq_mulHeight`, which is the only place where the two normalizations
interact here.

Not every lemma of `Mathlib.NumberTheory.Height.Basic` has an Arakelov analogue, and the two that
fail are not edge cases. `Height.mulHeight_pow` is **false** here — the ℓ² norm is not
multiplicative under coordinatewise powers — and with it `mulHeight₁_pow` and `mulHeight₁_zpow`.
`Height.mulHeight_comp_le` is **false** for a non-injective reindexing, since repeating a
coordinate raises the ℓ² norm at the archimedean places while no sup norm can see the repetition;
it is the injective case that its consumers use. Both are refuted among the examples at the end of
this file.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
(2006), Definition 2.8.1 and 2.8.2–2.8.3, where `H_u` is the local factor above and `h_Ar` the
resulting height on projective space. Their `h_Ar` is the *absolute* height — its local
exponent is `[F_w : ℚ_p] / [F : ℚ]` — whereas `arakelovMulHeight` here is *relative* to `K`,
matching Mathlib's `Height.mulHeight`; the two differ by the exponent `[K : ℚ]`.

This is Layers 0.1 and 0.2 of the `ArithmeticHeights` roadmap: the normalization and its
comparison with `Height.mulHeight`.
-/
public section
namespace NumberField
open Finset Function Height Real
variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']
/-- The **Arakelov height** of a tuple of elements of a number field: the ℓ² norm at the
archimedean places, weighted by `InfinitePlace.mult`, and the sup norm at the finite places.
For the zero tuple we take the junk value `1`, as `Height.mulHeight` does.

This is the normalization in which the constants of the Siegel-lemma literature are stated;
`Height.mulHeight` uses the sup norm at every place. Both live in the library and every bound
says which one it is in. -/
@[expose] noncomputable def arakelovMulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)

/-!
### Scaling invariance

The archimedean local factor scales by `v c ^ mult v` and the finite one by `v c`, so the
product formula makes the height invariant. The finite half of that computation is already in
Mathlib, inside `Height.mulHeight_smul_eq_mulHeight`; we read it off rather than redo it.
-/
section Smul
variable {κ : Type*}

end Smul
/-!
### Positivity and reindexing
-/

/-!
### Special values

`Height.mulHeight (1 : ι → K) = 1` by the product formula, but the Arakelov height of the same
tuple is `#ι ^ (totalWeight K / 2)`: these are the values that exhibit the difference between
the two normalizations without touching the junk value.
-/

/-!
### The comparison with the sup-norm height

`‖·‖_∞ ≤ ‖·‖_2 ≤ √(#ι) · ‖·‖_∞` at each archimedean place, raised to the weight `mult v` and
multiplied over the places; the finite parts of the two heights are the same number and factor
out. This is Layer 0.2 of the roadmap: the pair of lemmas that transports a constant stated for
the Arakelov height into Mathlib's normalization and back, and so the reason a bound in either
normalization is a bound in the other.

The constant of the upper comparison cannot be improved: at the all-ones tuple it is an equality,
by `arakelovMulHeight_one` against `Height.mulHeight_one`.
-/
section Comparison

end Comparison
/-!
### The one-variable case

`arakelovMulHeight₁ x` is the Arakelov height of the point `(x : 1)` of the projective line.
Unlike the sup-norm normalization, its archimedean local factor is `((v x) ^ 2 + 1) ^ (mult v / 2)`
rather than `max (v x) 1 ^ mult v`, so it does **not** agree with `Height.mulHeight₁`.
-/

/-!
The comparison of Layer 0.2, applied to `![x, 1]`. This is the only relation between the two
one-variable heights: `arakelovMulHeight₁ = mulHeight₁` is false, already at `x = 1`.
-/

end NumberField
/-!
### The descent to projective space

Scaling invariance makes the Arakelov height a well-defined function on
`Projectivization K (ι → K)`, exactly as for `Projectivization.mulHeight`.
-/
namespace Projectivization
open NumberField Real
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/-!
#### Comparison of the two normalizations on projective space

`NumberField.mulHeight_le_arakelovMulHeight` and `NumberField.arakelovMulHeight_le_mulHeight` read
on `Projectivization K (ι → K)`. Both sides are computed on any representative, so the comparisons
descend to projective space with the same constant.
-/

end Projectivization
/-!
### `positivity` extensions

The Arakelov heights are positive (multiplicative) resp. nonnegative (logarithmic), exactly as
their sup-norm counterparts in `Mathlib.NumberTheory.Height.Basic`.
-/
namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

end Mathlib.Meta.Positivity
/-!
### Worked examples

Cheap checks that the definition means what it should. Over `ℚ` the two normalizations of the
height of the point `(1 : 1)` genuinely differ, so the `√N` factors in the Siegel-lemma
literature are not cosmetic and a proof that silently interchanges the two heights is wrong.

The third shows that the constant of `arakelovMulHeight_le_mulHeight` is attained, so it cannot be
improved. The last two are rejection tests: they refute the two lemmas of
`Mathlib.NumberTheory.Height.Basic` that a reader would expect to carry over to this normalization
and that do not.
-/
section Examples
open Height NumberField
end Examples
end

end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.va75ab00733d7.ArithmeticHeights.MixedLattice ====
public section
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The mixed space of tuples, and the archimedean local factor as a determinant

For a number field `K` and a finite index type `ι`, the euclidean mixed space of `ι`-tuples is
`mixedPi K ι = PiLp 2 (fun _ : ι ↦ euclidean.mixedSpace K)`: the real carrier `(K ⊗ ℝ)ⁱ` of `Kⁱ`,
with the inner product for which the image of `(𝓞 K)ⁱ` is a lattice of the covolume Mathlib's
`covolume_integerLattice` computes. This file gives that space its trace form, attaches to a
matrix `Y` over the mixed space the `ℝ`-linear map of tuple spaces it defines, and identifies the
determinant of the associated Gram endomorphism `Y Yᴴ` with the archimedean local factor of the
Arakelov height of the Plücker point of `Y`.

That last identification is **Schmidt's Lemma 4**, and it is the archimedean half of the covolume
identity of Layer 4.3.

## Main definitions

* `NumberField.mixedEmbedding.mixedTrace`: the real trace functional on the mixed space, the sum
  of the real coordinates and of the real parts of the complex ones.
* `NumberField.mixedEmbedding.mixedPi`: the euclidean mixed space of `ι`-tuples.
* `NumberField.mixedEmbedding.toMixedPi`: the identification of `ι → mixedSpace K` with it.
* `NumberField.mixedEmbedding.mixedPiMap`: the `ℝ`-linear map `mixedPi K κ → mixedPi K ι` a matrix
  `Y : Matrix κ ι (mixedSpace K)` defines, acting by `u ↦ Yᵀ *ᵥ u`.
* `NumberField.mixedEmbedding.mixedPiEnd`: the endomorphism `Y Yᴴ` of `mixedPi K κ`.

## Main results

* `NumberField.mixedEmbedding.inner_euclidean`: `⟪a, b⟫ = mixedTrace (star a * b)`. The inner
  product of the euclidean mixed space is a trace form, so multiplication by an element of the
  mixed space has `star` for its adjoint.
* `NumberField.mixedEmbedding.inner_mixedPiMap`: `⟪Y x, Y y⟫ = ⟪(Y Yᴴ) x, y⟫`, the statement that
  `mixedPiEnd Y` is the Gram operator of `mixedPiMap Y`.
* `NumberField.mixedEmbedding.det_mixedPiEnd`: its determinant is `Algebra.norm ℝ (det (Y Yᴴ))`.
* `NumberField.mixedEmbedding.norm_mixedSpace`: the algebra norm on the mixed space is
  `∏_{w real} z_w · ∏_{w complex} |z_w|²`.
* `NumberField.mixedEmbedding.norm_det_gram`: **Schmidt's Lemma 4**, the composite
  `Algebra.norm ℝ (det (ι(Y) ι(Y)ᴴ)) = ∏_{v | ∞} (∑ₛ v(pₛ)²)^{mult v}` for `p` the Plücker point
  of a matrix `Y` over `K`.

## Implementation notes

⚠ **The archimedean half is Cauchy–Binet over the commutative star ring `mixedSpace K`, not a
place-by-place computation.** The mixed space is a product of copies of `ℝ` and `ℂ`, hence a
commutative `ℝ`-algebra with a star operation — the identity on the real factors and complex
conjugation on the complex ones. Over it, `Matrix.det_mul_conjTranspose_self_eq_sum` of Layer 3.4
computes `det (Y Yᴴ)` as `∑ₛ pₛ · star pₛ` in one step, and `exteriorPower.plucker_map` identifies
`p` with the mixed embedding of the Plücker point over `K`. The descent to `ℝ` is then
`LinearMap.det_restrictScalars`: the real determinant of a `mixedSpace K`-linear endomorphism is
the algebra norm of its mixed determinant. **Nothing is ever decomposed by place**, and the
`2^{−r₂}` of the milestone never appears here — it enters only through the covolume of `𝓞 K`.

⚠ **The adjoint is never constructed.** `ZLattice.det_gram_of_inner` asks only for *some* operator
`A` with `⟪f x, f y⟫ = ⟪A x, y⟫`, and `mixedPiEnd Y` is that operator by a one-line matrix identity
(`sum_star_mulVec`) together with the trace-form description of the inner product. So
`LinearMap.adjoint` and its finite-dimensional hypotheses stay out of the development.

⚠ **Instance search on this space is expensive**, because `mixedPi K ι` is a `PiLp` over a `WithLp`
of a product of two `PiLp`s, and the index types of the last two are subtypes of `InfinitePlace K`
that only a classical `Fintype` instance sees. The `Prop`-valued instances (`BorelSpace`,
`FiniteDimensional`) are therefore declared once here rather than rediscovered at every use site;
without them the elaboration of the covolume identity exceeds the default heartbeat budget.

## References

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, Lemma 4, which is `norm_det_gram` composed with the
covolume of `𝓞 K`.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, the archimedean half of the number-field
case.
-/
public section
noncomputable section
namespace NumberField.mixedEmbedding
open Module MeasureTheory Matrix NumberField.InfinitePlace
open scoped ComplexConjugate
variable (K : Type*) [Field K] [NumberField K]

variable {K}

variable (K)
open scoped Classical in
/-- The mixed space of `ι`-tuples, as a euclidean space: this is the ambient in which the lattice
of integral points of a subspace of `Kⁱ` lives. -/
abbrev mixedPi (ι : Type*) := PiLp 2 (fun _ : ι ↦ euclidean.mixedSpace K)
open scoped Classical in
/-- Reading a tuple of mixed-space points as a point of the euclidean tuple space. -/
@[expose] def toMixedPi (ι : Type*) : (ι → mixedSpace K) ≃ₗ[ℝ] mixedPi K ι :=
  (LinearEquiv.piCongrRight fun _ ↦ (euclidean.toMixed K).symm.toLinearEquiv).trans
    (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).symm

variable {K}

section Matrices
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

end Matrices
section Archimedean
open exteriorPower
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

end Archimedean
end NumberField.mixedEmbedding
end
end

end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.va75ab00733d7.ArithmeticHeights.NumberFieldLattice ====
public section
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The lattice of integral points of a subspace of a number field

For a subspace `V ⊆ Kⁱ` of dimension `k` over a number field `K`, the integral points
`V ∩ (𝓞 K)ⁱ` form a lattice of rank `[K : ℚ] · k` in the real span of `V` inside the euclidean
mixed space of `ι`-tuples, and its covolume is

```text
covol (V ∩ (𝓞 K)ⁱ)  =  (2^{−r₂} |discr K|^{1/2}) ^ k · H_Ar(V)
                    =  2^{−r₂ k} · |discr K|^{k/2} · H_Ar(V),
```

with `H_Ar` the Arakelov subspace height of Layer 3.2 relative to `K` — so the *absolute* height
enters with the exponent `[K : ℚ]`. This is **W. M. Schmidt 1967, §3, Theorem 1**, and it is the
computation that converts the lattice statement of Minkowski's second theorem into a height
statement. Over `ℚ` every constant is `1` and the identity is
`Submodule.covolume_intLattice` of `ArithmeticHeights/RationalLattice.lean`.

## Main definitions

* `NumberField.integralTuples`: the tuples of algebraic integers, inside `Kⁱ`.
* `Submodule.integerPoints`: the integral points `V ∩ (𝓞 K)ⁱ` of a subspace, an `𝓞 K`-submodule.
* `NumberField.mixedPiEmb`: the embedding of `Kⁱ` into the euclidean mixed space of tuples.
* `Submodule.mixedSpan`: the real span of `V` there.
* `Submodule.mixedLattice`: the integral points read inside that span — the object whose covolume
  the milestone computes.

## Main results

* `Submodule.covolume_mixedLattice`: the covolume identity displayed above.
* `Submodule.prod_mul_plucker_eq_one`: **primitivity** — for a pseudo-basis `(𝔞ᵢ, yᵢ)` of the
  integral points, `(∏ᵢ 𝔞ᵢ) · (p) = 𝓞 K`, with `(p)` the ideal generated by the Plücker
  coordinates of `y`. This is the finite half, and the only place saturation is used.
* `Submodule.exists_pseudoBasis_integerPoints`: the integral points have a pseudo-basis whose
  vectors are themselves integral points, so that the Plücker coordinates are integral.
* `NumberField.exists_idealBasis`: a nonzero fractional ideal is a lattice of covolume
  `N(𝔞) · 2^{−r₂} |discr K|^{1/2}` in the euclidean mixed space, with a `ℤ`-basis indexed by
  `Fin [K : ℚ]`.
* `NumberField.det_gram_pi`: the Gram determinant of a basis of `(K ⊗ ℝ)^k` assembled from bases of
  the factors is the product of theirs — the euclidean space of `k`-tuples is an orthogonal sum.
* `Submodule.finrank_mixedSpan`: the real span has dimension `[K : ℚ] · dim V`, and the
  `DiscreteTopology` and `IsZLattice` instances that make the covolume meaningful.

## Implementation notes

⚠ **Schmidt's Lemmas 5 and 6 — the local counting behind `[σ(Λ) : Λ₀] = N(𝔞)` — are not needed.**
They exist in his proof to compare the possibly non-free module `Λ = V ∩ (𝓞 K)ⁱ` with the free
`Λ₀ = ⊕ 𝓞 K yᵢ` generated by a `K`-basis inside it. A **pseudo-basis** `Λ = ⊕ 𝔞ᵢ yᵢ` removes the
comparison: the covolume of `⊕ 𝔞ᵢ` is `∏ᵢ N(𝔞ᵢ)` times that of `(𝓞 K)^k` by an orthogonal
block-diagonal Gram determinant, and what remains of the finite half is the single statement
`(∏ᵢ 𝔞ᵢ) · (p) = 𝓞 K`. No index of lattices is ever computed.

⚠ **Primitivity needs no localization and no uniformizer.** Suppose the Plücker ideal `𝔠` were
contained in a maximal `𝔮`. Choose `aᵢ ∈ 𝔞ᵢ ∖ 𝔮𝔞ᵢ`; then all the maximal minors of the integral
family `aᵢ yᵢ` lie in `𝔮`, so their reductions are dependent over the residue field —
`exteriorPower.plucker_eq_zero_iff` of Layer 3.1 read over `𝓞 K ⧸ 𝔮` — and some combination
`u = ∑ cᵢ aᵢ yᵢ` has all coordinates in `𝔮`. Multiplying `u` by any `t ∈ 𝔮⁻¹` therefore lands in
`(𝓞 K)ⁱ`, hence in `V ∩ (𝓞 K)ⁱ` by **saturation**; reading off coefficients gives
`𝔮⁻¹ cᵢaᵢ ⊆ 𝔞ᵢ`, so `cᵢaᵢ ∈ 𝔮𝔞ᵢ` and `cᵢ ∈ 𝔮` for every `i` — a contradiction. The only
arithmetic used is `𝔮 𝔮⁻¹ = 𝓞 K`. Over `ℚ` this argument degenerates to the division by a prime
`q` of `Submodule.gcd_plucker_eq_one`.

⚠ **The integrality of the Plücker point is a normalization of the pseudo-basis, not a lemma.**
Scaling `yᵢ` by a nonzero `a ∈ 𝔞ᵢ` and `𝔞ᵢ` by `a⁻¹` changes neither the module nor the span and
puts every `yᵢ` inside `V ∩ (𝓞 K)ⁱ`; the minors are then algebraic integers, which is what lets
the finite places read them through `NumberField.FinitePlace.finprod_iSup_eq_inv_absNorm`.

⚠ **Instances are declared, not searched.** `MeasureSpace`, `BorelSpace`, `FiniteDimensional` and
`IsAddHaarMeasure` for the real span are given once each; the nested `WithLp` structure of the
mixed space otherwise makes every use site re-derive them and exceed the heartbeat budget.

## References

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, Theorem 1 (`H'(S) = H(S)`), whose normalization this is:
his `ρ` is the `(Re, Im)` embedding and his `Δ = 2^{−r₂} |𝔡|^{1/2}` the covolume of `𝓞 K`.

J. L. Thunder, "An adelic Minkowski–Hlawka theorem and an application to Siegel's lemma",
*Journal für die reine und angewandte Mathematik* **475** (1996), 167–185, and
"Siegel's lemma for function fields", where the same identity is stated in a conjugate-pairs
embedding, which is why no `2^{−r₂}` appears there.

E. Steinitz, "Rechteckige Systeme und Moduln in algebraischen Zahlkörpern", *Mathematische
Annalen* **71** (1911), 328–354, for the pseudo-basis that replaces Schmidt's free sublattice.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, over a number field.
-/
public section
noncomputable section
open Module NumberField NumberField.mixedEmbedding
variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-!
### The integral points are a finitely generated module spanning the subspace
-/
section Data
open scoped nonZeroDivisors
variable [Finite ι]

end Data
section Defs
variable [Finite ι]
open scoped Classical in
/-- The embedding of `Kⁱ` into the euclidean mixed space of `ι`-tuples. -/
@[expose] def mixedPiEmb (K : Type*) [Field K] [NumberField K] (ι : Type*) :
    (ι → K) →ₗ[ℤ] mixedPi K ι :=
  (LinearMap.restrictScalars ℤ (toMixedPi K ι).toLinearMap) ∘ₗ
    AddMonoidHom.toIntLinearMap (AddMonoidHom.pi fun l ↦
      (mixedEmbedding K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : ι ↦ K) l))

end Defs
variable [Fintype ι]

/-!
### The lattice of a fractional ideal in the euclidean mixed space
-/
section IdealBasis
open scoped nonZeroDivisors
open Real NumberField.InfinitePlace

end IdealBasis
/-!
### The Gram determinant of a product basis
-/
section Product
open Matrix

end Product
/-!
### Primitivity of the Plücker point
-/
section Primitive
open exteriorPower
open scoped nonZeroDivisors

variable [LinearOrder ι]

variable (V : Submodule K (ι → K)) {k : ℕ} {y : Fin k → (ι → K)}
  {𝔞 : Fin k → FractionalIdeal (𝓞 K)⁰ K} {p : Set.powersetCard ι k → 𝓞 K}

end Primitive
/-!
### The map attached to a `K`-basis of the subspace
-/
section Assembly
open exteriorPower Matrix
variable [LinearOrder ι]

section Finiteness
omit [Fintype ι]
variable [Finite ι]

end Finiteness

end Assembly
/-!
### Two readings of integrality

The finite half of the height of an integral tuple, and the membership test for the lattice of
integral points. Both are consumed by the Bombieri–Vaaler milestones of Layer 5, which differ in
their convex body but not in how they read integrality.
-/
namespace NumberField.mixedEmbedding
open Module NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

end NumberField.mixedEmbedding
end
end

end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.va75ab00733d7.ArithmeticHeights.MixedBall ====
public section
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The ℓ² body of a number field and the volume of its slices

For a number field `K` and a finite index type `κ`, the euclidean tuple space `mixedPi K κ` of
Layer 4.3 carries the convex body

```text
mixedBall K κ  =  { x : ∀ v | ∞, ‖x_v‖₂ ≤ 1 },
```

the product over the infinite places of the unit balls of the ℓ² norms of the local coordinates.
This file computes the volume of its slice by the real span of a `K`-subspace `V ⊆ Kⁱ`:

```text
vol (mixedBall K ι ∩ V_ℝ)  =  ω_k ^ r₁ · ω_{2k} ^ r₂,      k = dim_K V,
```

`ω_n` the volume of the unit ball of `ℝⁿ`. **At each infinite place the slice of a euclidean ball
by a subspace is a euclidean ball of the smaller dimension**, which is why Layer 5.3 needs no
slicing inequality — unlike Layer 5.4, whose body is a product of cubes and polydiscs.

## Main definitions

* `NumberField.mixedEmbedding.mixedIndex`: the index type of the standard real coordinates of the
  euclidean tuple space, one block per infinite place.
* `NumberField.mixedEmbedding.toMixedTuple`, `NumberField.mixedEmbedding.mixedPiIsometry`: those
  coordinates, as a linear equivalence and as a linear isometry from a euclidean space.
* `NumberField.mixedEmbedding.realPart`, `NumberField.mixedEmbedding.complexPart`: the local
  coordinate tuple at a real, respectively complex, place.
* `NumberField.mixedEmbedding.mixedBall`: the body itself.
* `NumberField.mixedEmbedding.ofLocal`: the matrix over the mixed space assembled from a family
  of matrices over `ℝ` and `ℂ`, one per infinite place.

## Main results

* `NumberField.mixedEmbedding.volume_mixedBall`: the volume of the body is
  `ω_{#κ} ^ r₁ · ω_{2 #κ} ^ r₂`.
* `NumberField.mixedEmbedding.volume_preimage_mixedBall_mixedSpan`: **the slice bound**, the
  displayed identity above, with the slice measured inside the real span of `V`.
* `Matrix.exists_mul_conjTranspose_eq_one`: **local orthonormalization**, a matrix over `ℝ` or `ℂ`
  with nonzero Gram determinant becomes orthonormal after an invertible row operation.
* `NumberField.mixedEmbedding.exists_ofLocal_eq_mul`: the same over the mixed space, place by
  place, which is what produces an *isometry* onto the real span.
* `MeasureTheory.measurePreserving_uncurry`: a product measure over a product index type is the
  iterated product measure.
* `MeasureTheory.volume_prodSqBall`: the volume of a product of ℓ² unit balls.

## Implementation notes

⚠ **The slice is computed by moving the lattice's ambient space, not by slicing.** A `K`-basis `y`
of `V` gives a map `mixedPiMap Y` of euclidean tuple spaces whose range is the real span of `V`,
but which is not an isometry. Orthonormalizing `Y` *at each infinite place* — `LDL` over `ℝ` and
over `ℂ`, assembled by `ofLocal` — replaces it by `E = M Y` with `E Eᴴ = 1` locally, and then
`mixedPiMap E` is an isometry with the same range, carrying `mixedBall K (Fin k)` onto the slice.
The volume of the slice is therefore the volume of the *whole* body in a smaller tuple space,
where no subspace appears at all.

⚠ **The ranges are compared by dimension, so `M` never has to be inverted.** `E = M Y` gives
`range (mixedPiMap E) ≤ range (mixedPiMap Y)` for free, both maps are injective, and the real span
of `V` sits inside the second range because every element of `V` is a `K`-combination of the `y`'s.
All three subspaces have dimension `[K : ℚ] · k`, so all three coincide.

⚠ **The volume of the body is a product measure computation in coordinates.** The standard real
coordinates identify `mixedPi K κ` isometrically with `EuclideanSpace ℝ (mixedIndex K κ)`, and the
body becomes a product over the places of ℓ² unit balls in `κ`, respectively `κ ⊕ κ`, coordinates.
Turning that into `∏` of volumes needs the currying `Measure.pi (fun _ : α × β ↦ μ) =
Measure.pi (fun _ : α ↦ Measure.pi fun _ : β ↦ μ)`, which Mathlib has for sums of index types but
not for products; `MeasureTheory.measurePreserving_uncurry` supplies it.

⚠ **`Matrix.PosSemidef` has no square root in Mathlib**, so the local orthonormalization goes
through the `LDL` decomposition: `L S Lᴴ` is diagonal with positive entries, and a diagonal matrix
does have a square root. What is needed is only *some* `M` with `M S Mᴴ = 1`, not the symmetric
one.

## References

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), §I.

J. D. Vaaler, "The best constant in Siegel's lemma", *Monatshefte für Mathematik* **140** (2003),
71–89, where the inequality this file's slice bound feeds is quoted as (1.3).

This is Layer 5.3 (infrastructure) of the `ArithmeticHeights` roadmap.
-/
public section
namespace NumberField.mixedEmbedding
open Module MeasureTheory NumberField NumberField.InfinitePlace
variable (K : Type*) [Field K] [NumberField K] (κ : Type*)
/-- The index type of the standard real coordinates of the euclidean tuple space. -/
abbrev mixedIndex : Type _ :=
  ({w : InfinitePlace K // IsReal w} × κ) ⊕ ({w : InfinitePlace K // IsComplex w} × (κ ⊕ κ))
/-- Standard real coordinates on the tuples of mixed-space points. -/
@[expose] def toMixedTuple : (mixedIndex K κ → ℝ) ≃ₗ[ℝ] (κ → mixedSpace K) where
  toFun c := fun j ↦ (fun w ↦ c (.inl (w, j)),
    fun w ↦ ⟨c (.inr (w, .inl j)), c (.inr (w, .inr j))⟩)
  invFun u := Sum.elim (fun p ↦ (u p.2).1 p.1)
    (fun q ↦ Sum.elim (fun j ↦ ((u j).2 q.1).re) (fun j ↦ ((u j).2 q.1).im) q.2)
  map_add' _ _ := rfl
  map_smul' r c := by
    ext j
    · rfl
    · simp [Complex.ext_iff, Complex.real_smul]
  left_inv c := by
    ext idx
    rcases idx with p | ⟨w, j | j⟩ <;> rfl
  right_inv u := by
    ext j
    · rfl
    · rfl
variable {K κ}

variable [Fintype κ]
open scoped Classical in
set_option linter.unusedVariables false in
axiom _root_.NumberField.mixedEmbedding.inner_toMixedPi_toMixedTuple.{w_u_1,w_u_2} : ∀ {K : Type w_u_1} [inst : Field K] [inst_1 : NumberField K] {κ : Type w_u_2} [inst_2 : Fintype κ]
  (c c' : NumberField.mixedEmbedding.mixedIndex K κ → ℝ),
  Inner.inner ℝ
      ((NumberField.mixedEmbedding.toMixedPi K κ :
          (κ → NumberField.mixedEmbedding.mixedSpace K) → NumberField.mixedEmbedding.mixedPi K κ)
        ((NumberField.mixedEmbedding.toMixedTuple K κ :
            (NumberField.mixedEmbedding.mixedIndex K κ → ℝ) →
              κ → NumberField.mixedEmbedding.mixedSpace K)
          c))
      ((NumberField.mixedEmbedding.toMixedPi K κ :
          (κ → NumberField.mixedEmbedding.mixedSpace K) → NumberField.mixedEmbedding.mixedPi K κ)
        ((NumberField.mixedEmbedding.toMixedTuple K κ :
            (NumberField.mixedEmbedding.mixedIndex K κ → ℝ) →
              κ → NumberField.mixedEmbedding.mixedSpace K)
          c')) =
    ∑ idx : NumberField.mixedEmbedding.mixedIndex K κ, c idx * c' idx
variable (K κ)
open scoped Classical in
/-- The standard real coordinates identify the euclidean tuple space with a euclidean space. -/
@[expose] noncomputable def mixedPiIsometry :
    EuclideanSpace ℝ (mixedIndex K κ) ≃ₗᵢ[ℝ] mixedPi K κ :=
  LinearEquiv.isometryOfInner
    (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
      (toMixedPi K κ))
    (fun x y ↦ by
      rw [show (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
            (toMixedPi K κ)) x
          = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp x)) from rfl,
        show (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
            (toMixedPi K κ)) y
          = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp y)) from rfl,
        inner_toMixedPi_toMixedTuple, PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by
        change WithLp.ofLp x i * WithLp.ofLp y i = inner ℝ (WithLp.ofLp x i) (WithLp.ofLp y i)
        rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm])

end NumberField.mixedEmbedding
namespace MeasureTheory

end MeasureTheory
namespace MeasureTheory
open Metric

end MeasureTheory
namespace NumberField.mixedEmbedding
open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise
variable (K : Type*) [Field K] [NumberField K] (κ : Type*) [Fintype κ]
open scoped Classical in
/-- The tuple of coordinates of a point of the euclidean tuple space at a real place. -/
@[expose] noncomputable def realPart (w : {w : InfinitePlace K // IsReal w}) :
    mixedPi K κ →ₗ[ℝ] EuclideanSpace ℝ κ where
  toFun x := WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).1 w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
open scoped Classical in
/-- The tuple of coordinates of a point of the euclidean tuple space at a complex place. -/
@[expose] noncomputable def complexPart (w : {w : InfinitePlace K // IsComplex w}) :
    mixedPi K κ →ₗ[ℝ] EuclideanSpace ℂ κ where
  toFun x := WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).2 w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- **The convex body of Layer 5.3**: the product over the infinite places of the unit balls of
the ℓ² norms of the local coordinates. -/
@[expose] noncomputable def mixedBall : Set (mixedPi K κ) :=
  (⋂ w : {w : InfinitePlace K // IsReal w}, realPart K κ w ⁻¹' Metric.closedBall 0 1) ∩
    ⋂ w : {w : InfinitePlace K // IsComplex w}, complexPart K κ w ⁻¹' Metric.closedBall 0 1
variable {K κ}

end NumberField.mixedEmbedding
namespace Matrix
open scoped ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {k : ℕ} {ι : Type*} [Fintype ι]

end Matrix
namespace NumberField.mixedEmbedding
open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {k : ℕ}

end NumberField.mixedEmbedding
namespace NumberField.mixedEmbedding
open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {k : ℕ}

end NumberField.mixedEmbedding

end
end

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_b8401c953af762e64c9b_BombieriVaalerField ====
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Bombieri–Vaaler over a number field: the Hermitian form

**Bombieri–Vaaler 1983; the inequality Vaaler 2003 quotes as (1.3).** Let `K` be a number field of
degree `d` with `r₁` real and `r₂` complex places and discriminant `D`, and let `V ⊆ Kⁱ` be a
subspace of dimension `k`. Then `V` has a basis `x₁, …, x_k` of vectors with coordinates in
`𝓞 K` and

```text
∏_{l} H_Ar(x l)  ≤  (2^k / ω_k)^{r₁} (2^k / ω_{2k})^{r₂} · |D|^{k/2} · H_Ar(V),
```

relative Arakelov heights on both sides, `ω_n` the volume of the unit ball of `ℝⁿ`; taking `d`-th
roots gives the absolute form the literature states. For `V` the solution space of `A x = 0` the
right-hand side is the Arakelov height of the **row space** of `A`, by the duality theorem of
Layer 3.5.

## Main results

* `NumberField.exists_basis_prod_arakelovMulHeight_le`: the displayed inequality.
* `NumberField.exists_basis_prod_arakelovMulHeight_rpow_le`: its absolute form, all heights raised
  to the power `1/d`.
* `NumberField.exists_basis_ker_prod_arakelovMulHeight_rpow_le`: the matrix form — a basis of the
  solution space of `A x = 0`, bounded by the Arakelov height of the row space of `A`.
* `NumberField.mixedEmbedding.arakelovMulHeight_le_of_mem_smul_mixedBall`: the height of an
  integral tuple lying in `λ · mixedBall` is at most `λ ^ d`.
* `NumberField.mixedEmbedding.prod_successiveMinimum_mixedBall_le`: Minkowski's second theorem for
  the ℓ² body, with the covolume of Layer 4.3 and the slice volume of `MixedBall.lean` inserted.

## Implementation notes

⚠ **The constant is `2^{d k}` from Layer 4.2 against `2^{−r₂ k}` from Layer 4.3, and what survives
is `2^{k(r₁ + r₂)}`.** Over `ℤ` the two powers of two cancelled exactly (Layer 5.2); here they do
not, because the unit balls of the ℓ² norms are not the unit cubes, and the residue
`(2^k/ω_k)^{r₁} (2^k/ω_{2k})^{r₂}` is exactly the ratio between a cube and a ball. Layer 5.4
replaces the balls by cubes and polydiscs, and that is where cube slicing is needed.

⚠ **The rank hypothesis of the milestone is unnecessary.** The matrix form is stated for an
arbitrary `A`: Layer 3.5's `Matrix.arakelovMulHeight_ker_mulVecLin` identifies the height of the
solution space with the height of the row space with no hypothesis on `A`, and the geometric half
never looks at `A` at all. Stating `LinearIndependent K A.row` would only fix `k = N − M`.

⚠ **`k = 0` needs no special case.** The empty product is `1`, and Minkowski's second theorem
applied to the zero-dimensional lattice gives `1 ≤ C · H_Ar(V)` directly; no value of `ω_0` is
ever needed. For the same reason the basis is built with `Basis.mk` and a rank count rather than
with `basisOfLinearIndependentOfCardEqFinrank`, which demands a nonempty index type.

⚠ **The extraction of Layer 4.4 is applied to `ℚ`-linearity, not `ℤ`-linearity.** The mixed
embedding is a `ℤ`-linear map, but the counting argument needs a map of `ℚ`-vector spaces;
`AddMonoidHom.toRatLinearMap` supplies it, since a `ℚ`-linear structure on an additive group is
unique.

## References

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), Theorem 9 and §I.

J. D. Vaaler, "The best constant in Siegel's lemma", *Monatshefte für Mathematik* **140** (2003),
71–89, (1.3).

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, for the covolume identity this consumes.

This is Layer 5.3 of the `ArithmeticHeights` roadmap.
-/
public section
namespace NumberField.mixedEmbedding
open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open scoped Pointwise
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
set_option linter.unusedVariables false in
/-- **The height of an integral tuple in a dilate of the body.** -/
theorem arakelovMulHeight_le_of_mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0) (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedBall K ι) 
    (h_NumberField_mixedEmbedding_sum_sq_le_of_mem_smul_mixedBall : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type u_2} [inst_2 : Fintype ι]
      {r : ℝ},
      0 < r →
        ∀ {x : ι → K},
          (mixedPiEmb K ι : (ι → K) → NumberField.mixedEmbedding.mixedPi K ι) x ∈
              r • NumberField.mixedEmbedding.mixedBall K ι →
            ∀ (w : NumberField.InfinitePlace K), ∑ j : ι, (w : K → ℝ) (x j) ^ 2 ≤ r ^ 2)
    (h_NumberField_mixedEmbedding_finprod_finitePlace_le_one : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type u_2} [Finite ι] {x : ι → K},
      x ≠ 0 →
        (∀ (l : ι), ∃ (z : NumberField.RingOfIntegers K), (↑z : K) = x l) →
          ∏ᶠ (v : NumberField.FinitePlace K), ⨆ (i : ι), (v : K → ℝ) (x i) ≤ 1)
    (h_NumberField_arakelovMulHeight_eq : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type u_2} [inst_2 : Fintype ι]
      {x : ι → K},
      x ≠ 0 →
        NumberField.arakelovMulHeight x =
          (∏ v : NumberField.InfinitePlace K, (∑ i : ι, (v : K → ℝ) (x i) ^ 2) ^ ((↑v.mult : ℝ) / 2)) *
            ∏ᶠ (v : NumberField.FinitePlace K), ⨆ (i : ι), (v : K → ℝ) (x i))
    :
    arakelovMulHeight x ≤ r ^ finrank ℚ K := by
  rw [h_NumberField_arakelovMulHeight_eq hx]
  have hpow : ∀ n : ℕ, ((r ^ 2 : ℝ)) ^ ((n : ℝ) / 2) = r ^ n := by
    intro n
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r n]
    congr 1
    push_cast
    ring
  have harch : (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
      ≤ r ^ finrank ℚ K := by
    calc (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
        ≤ ∏ w : InfinitePlace K, r ^ w.mult := by
          refine Finset.prod_le_prod₀ (fun w _ ↦ Real.rpow_nonneg (by positivity) _)
            fun w _ ↦ ?_
          rw [← hpow w.mult]
          exact Real.rpow_le_rpow (by positivity)
            (h_NumberField_mixedEmbedding_sum_sq_le_of_mem_smul_mixedBall hr hmem w) (by positivity)
      _ = r ^ (∑ w : InfinitePlace K, w.mult) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = r ^ finrank ℚ K := by rw [InfinitePlace.sum_mult_eq]
  have hfin := h_NumberField_mixedEmbedding_finprod_finitePlace_le_one hx hint
  have hfin0 : 0 ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  have harch0 : 0 ≤ ∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ) :=
    Finset.prod_nonneg fun w _ ↦ Real.rpow_nonneg (by positivity) _
  calc (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
        * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
      ≤ (r ^ finrank ℚ K) * 1 := mul_le_mul harch hfin hfin0 (by positivity)
    _ = r ^ finrank ℚ K := mul_one _
section Span
end Span
end NumberField.mixedEmbedding
namespace NumberField
section Main
end Main
section Kernel
end Kernel
end NumberField
