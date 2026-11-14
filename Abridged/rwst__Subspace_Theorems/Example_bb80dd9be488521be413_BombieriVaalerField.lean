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

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.Arakelov ====
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

axiom arakelovMulHeight_pos (x : ι → K) : 0 < arakelovMulHeight x

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
private axiom arakelovMulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K)
    (h : a.val = t • b.val) :
    NumberField.arakelovMulHeight a.val = NumberField.arakelovMulHeight b.val

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.
/-- The multiplicative Arakelov height of a point of projective space over a number field. -/
noncomputable def arakelovMulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ NumberField.arakelovMulHeight r.val) arakelovMulHeight_aux

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

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.Plucker ====
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
# The Plücker point of a subspace

A `k`-dimensional subspace `V` of `ι → K` determines a point of the projective space on
`Set.powersetCard ι k → K`, the tuple of its **Plücker coordinates**: wedge a basis of `V` together
inside `⋀[K]^k (ι → K)` and read the result in the basis that the standard basis of `ι → K`
induces there. A change of basis of `V` multiplies the wedge by a determinant, hence by a unit, so
the point of projective space depends on `V` alone.

This file builds that point and proves it is an embedding of the `k`-dimensional subspaces into
projective space. Layer 3.2 defines the height of a subspace as the height of this point, and
everything the height inherits — Northcott for subspaces above all — rests on the injectivity
proved here.

## Main definitions

* `exteriorPower.plucker k v` for `v : Fin k → (ι → K)`: the coordinate tuple of the wedge
  `v 0 ∧ ⋯ ∧ v (k-1)`, indexed by the `k`-element subsets of `ι`.
* `Submodule.pluckerPoint V hV` for `hV : Module.finrank K V = k`: the induced point of
  `Projectivization K (Set.powersetCard ι k → K)`.

## Main results

* `exteriorPower.plucker_apply`: the Plücker coordinate at `s` is the maximal minor on the columns
  `s` of the matrix whose rows are the `v i`. `exteriorPower.plucker_fin_eq_det` is the top-rank
  case, where the single coordinate is the determinant, and
  `exteriorPower.plucker_one_ofSingleton` the rank-one case, where the coordinates are the
  coordinates of the vector.
* `exteriorPower.plucker_eq_zero_iff`: the coordinate tuple vanishes exactly when the family is
  linearly dependent, so a basis of `V` produces a nonzero tuple.
* `Submodule.pluckerPoint_eq_mk` and `Submodule.pluckerPoint_span_range`: the value of the Plücker
  point on *any* basis of `V`, and on any linearly independent family spanning it. This is the
  basis-independence, stated in the form that is actually used.
  `Submodule.pluckerPoint_span_singleton` is the rank-one case: the Plücker point of a line is the
  point itself.
* `Submodule.pluckerPoint_injective`: distinct subspaces of the same rank have distinct Plücker
  points.

Two lemmas are stated here because Mathlib lacks them and the proofs need them:
`exteriorPower.ιMulti_eq_zero_iff`, that over a field a wedge vanishes exactly on linearly
dependent families, and `linearIndependent_fin1`, the `Fin 1` companion of Mathlib's
`linearIndependent_fin2`.

## Implementation notes

The index type is Mathlib's `Set.powersetCard ι k`, the type of `k`-element finsets of `ι`, because
that is what `Module.Basis.exteriorPower` is indexed by; using it verbatim is what lets
`exteriorPower.plucker_apply` come out of Mathlib's `exteriorPower.ιMultiDual_apply_ιMulti` with no
index bookkeeping of our own. It is also why `[LinearOrder ι]` is a standing hypothesis: an order
on `ι` is needed to say *which* wedge of basis vectors a `k`-element subset names. A different
order changes each coordinate by a sign only, so nothing downstream depends on the choice.

The Plücker point is *not* built by `Projectivization.lift`. There is no projective space to lift
from: the data that varies is a basis of `V`, and bases do not form a projectivization. What takes
its place is `Submodule.pluckerPoint_eq_mk`, which says the value on an arbitrary basis is the
value on the chosen one, and which is the only thing a proof ever needs from well-definedness.
The definition itself picks `Module.finBasisOfFinrankEq`.

Injectivity is proved through the wedge criterion `exteriorPower.ιMulti_snoc_eq_zero_iff`: a vector
lies in the span of a linearly independent family exactly when wedging it on gives `0`. Since the
wedge of a basis of `V` is recovered from the Plücker point up to a nonzero scalar, and scaling
does not change what the criterion detects, the point determines the subspace. The criterion itself
is proved in `ExteriorAlgebra K (ι → K)`, where wedging on is multiplication.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§2.8.4.

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000),
Exercise A.1.11(a)–(b).

This is Layer 3.1 of the `ArithmeticHeights` roadmap.
-/
public section
open Module
section LinearIndependent
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

end LinearIndependent
namespace exteriorPower

section Field
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] {k : ℕ}

end Field
section Snoc
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}

end Snoc
section Plucker
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]
/-- The **Plücker coordinates** of a family `v : Fin k → (ι → R)`: the coordinate tuple of the
wedge `v 0 ∧ ⋯ ∧ v (k-1)` in the basis of `⋀[R]^k (ι → R)` induced by the standard basis of
`ι → R`, indexed by the `k`-element subsets of `ι`. -/
@[expose] noncomputable def plucker (k : ℕ) (v : Fin k → (ι → R)) : Set.powersetCard ι k → R :=
  ((Pi.basisFun R ι).exteriorPower k).equivFun (ιMulti R k v)

variable {K : Type*} [Field K] {k : ℕ} {v : Fin k → (ι → K)}

/-- Over a field, the Plücker coordinates of a linearly independent family are not all zero. -/
axiom plucker_ne_zero (hv : LinearIndependent K v) : plucker k v ≠ 0

end Plucker
end exteriorPower
namespace Submodule
open exteriorPower
section Basis
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {κ : Type*}
  {V : Submodule R M}
/-- The family of vectors of `M` underlying a basis of a submodule is linearly independent. -/
axiom linearIndependent_coe_basis (b : Basis κ R V) : LinearIndependent R fun i ↦ ((b i : M))

end Basis
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

/-- **The Plücker point of a `k`-dimensional subspace of `ι → K`** (Bombieri–Gubler 2.8.4;
Hindry–Silverman, Exercise A.1.11(a)–(b)): the point of projective space on the `k`-element subsets
of `ι` given by the Plücker coordinates of any basis of `V`. It does not depend on the basis; see
`Submodule.pluckerPoint_eq_mk`. -/
@[expose] noncomputable def pluckerPoint (V : Submodule K (ι → K)) (hV : finrank K V = k) :
    Projectivization K (Set.powersetCard ι k → K) :=
  Projectivization.mk K (plucker k fun i ↦ (((finBasisOfFinrankEq K V hV) i : ι → K)))
    (plucker_ne_zero (linearIndependent_coe_basis _))

end Submodule
section Examples
open Submodule exteriorPower
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]
end Examples

end
end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.Subspace ====
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
# The height of a linear subspace

Schmidt's height of a subspace `V : Submodule K (ι → K)`: the height of its Plücker point
`Submodule.pluckerPoint`, a point of `Projectivization K (Set.powersetCard ι k → K)`, in each of
the three normalizations the roadmap carries — Mathlib's sup-norm height, the Arakelov height of
Layer 0.1, and the absolute height of Layer 0.4 — with the logarithmic form of each alongside.

The definition is Bombieri–Gubler 2.8.4 and Schmidt 1967, §1. What makes it the right definition
is `Submodule.mulHeight_span_singleton`: the height of a line is the projective height of the
point that spans it.

## Main definitions

* `Submodule.mulHeight`, `Submodule.logHeight`: the height of a subspace of `ι → K`, over any
  field with `Height.AdmissibleAbsValues`.
* `Submodule.arakelovMulHeight`, `Submodule.arakelovLogHeight`: the ℓ²-at-infinity variant, over a
  number field.
* `Submodule.absMulHeight`, `Submodule.absLogHeight`: the absolute variant, over a field of
  algebraic numbers.

## Main results

* `Submodule.mulHeight_span_singleton`: `Submodule.mulHeight (span K {x}) = Height.mulHeight x`
  for `x ≠ 0`, and the same for the other three heights. This is the compatibility that fixes the
  definition; it is `exteriorPower.plucker_one_comp` of Layer 3.1 read through
  `Height.mulHeight_comp_equiv`.
* `Submodule.mulHeight_span_range`: the height of the span of a linearly independent family is
  the height of its tuple of Plücker coordinates, which by `exteriorPower.plucker_apply` is its
  tuple of maximal minors. This is the form the matrix dictionary of 3.3 consumes.
* `Submodule.mulHeight_bot` and `Submodule.mulHeight_top`: the two degenerate ranks, where the
  exterior power is a line, have height `1`.
* `Submodule.one_le_mulHeight`, and positivity and nonnegativity beside it.
* `Submodule.mulHeight_eq_mulHeight_pluckerPoint`: the definition, re-typed along any proof that
  the rank of `V` is `k`. Every proof enters through this rather than through the definition.
* `Submodule.absMulHeight_eq`: over a number field the absolute height of a subspace is the
  relative one normalized by the degree, as it is for tuples and for projective points.
* `Submodule.mulHeight_le_arakelovMulHeight`: the height of a subspace is at most its Arakelov
  height, the comparison of Layer 0.2 read at the Plücker point.

`Set.powersetCard.subsingleton_iff` and `Projectivization.mulHeight_eq_one_of_subsingleton` are
stated here because Mathlib has neither, although both are about Mathlib's own objects — the first
sits beside `Set.powersetCard.nontrivial_iff`, the second beside
`Projectivization.mulHeight`. They belong upstream rather than in this library.

## Implementation notes

The rank is not a parameter of the definition. `Submodule.mulHeight V` is
`Projectivization.mulHeight (V.pluckerPoint rfl)`, taking `k := Module.finrank K V`, so it is a
total function of `V` alone: `Submodule.mulHeight (V ⊓ W)` is well formed without producing a rank
for `V ⊓ W` first, which is what the submodularity of 3.6 needs.
`Submodule.mulHeight_eq_mulHeight_pluckerPoint` re-types it along an arbitrary
`hV : Module.finrank K V = k` — by `subst`, since `k` is a variable — and that lemma, not the
definition, is what every proof below uses.

Both degenerate cases are one argument, and neither is a computation of Plücker coordinates: for
`Module.finrank K V = 0` and for `Module.finrank K V = Fintype.card ι` the index type
`Set.powersetCard ι (Module.finrank K V)` is a subsingleton — only `∅`, only `Finset.univ` — so
every tuple over it has height `1` by the product formula. In particular `mulHeight ⊤ = 1` does
not go through `exteriorPower.plucker_fin_eq_det`, which is stated for `ι = Fin n`.

The four height families are separate sections rather than one definition parametrized by a
height, because their hypotheses differ: `Height.AdmissibleAbsValues K` for the first,
`NumberField K` for the Arakelov height, and `CharZero K` with `Algebra.IsAlgebraic ℚ K` for the
absolute one. As the roadmap's convention records, the duplication is in the statements only.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.8.4 for the height of a subspace and Definition 2.8.11 for its Arakelov normalization; their
`h(V)` and `h_Ar(V)` are absolute, ours relative, as everywhere in this development.
W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §1, where the height of a subspace is defined through its
Grassmann coordinates for the first time.

This is Layer 3.2 of the `ArithmeticHeights` roadmap.
-/
public section
open Module
/-!
### Two lemmas that belong upstream

`Set.powersetCard.nontrivial_iff` is in Mathlib; its negation is not, and it is what makes the two
degenerate ranks of a subspace height degenerate. Mathlib's `Projectivization.mulHeight` has no
subsingleton lemma either, although the tuple-level `Height.mulHeight_eq_one_of_subsingleton` is
there.
-/
namespace Set.powersetCard

end Set.powersetCard
namespace Projectivization
variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι]

end Projectivization
namespace Submodule
open exteriorPower
section Degenerate
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {V : Submodule K (ι → K)}

end Degenerate
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}
/-!
### The height of a subspace
-/
section Relative
variable [Height.AdmissibleAbsValues K]

end Relative
/-!
### The Arakelov height of a subspace

The same definition with the ℓ² norm at the archimedean places, which is the normalization the
Siegel-lemma literature states its constants in.
-/
section Arakelov
variable [NumberField K]
/-- **The multiplicative Arakelov height of a linear subspace of `ι → K`**, `H_Ar(V)` of
Bombieri–Gubler 2.8.11. -/
noncomputable def arakelovMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovMulHeight (V.pluckerPoint rfl)

end Arakelov
/-!
### The absolute height of a subspace

The variant that does not depend on the field the subspace is written over; it is the one the
literature's `h(V)` is, and one of the six Northcott statements of 3.7.
-/
section Absolute
variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

end Absolute
end Submodule
/-!
### Worked examples
-/
section Examples
open Submodule
end Examples
end

end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.Extraction ====
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
# The extraction lemma: independence over a subfield, back over the field

Let `F ⊆ K` be a finite field extension of degree `d = finrank F K`, let `V` be a `K`-vector
space, and let `f : V →ₗ[F] W` be an `F`-linear map into a vector space `W` over a third field
`E ⊇ F`. If the images `f (u i)` of a finite family `u : ι → V` are linearly independent *over
`E`*, then `u` spans a `K`-subspace of dimension at least `#ι / d`, and one can *select* from `u`
a `K`-linearly independent subfamily whose indices are controlled.

Nothing here is number theory: it is the counting that converts independence over a large field
back into independence over a small one, and a greedy selection on top of it.

## Main results

* `LinearIndependent.fintype_card_le_finrank_mul_finrank_span`: the counting half,
  `#ι ≤ finrank F K * finrank K (span K (range u))`.
* `exists_linearIndependent_comp_of_lt_finrank_span`: the selection half, under arbitrary index
  bounds. If for each `j < k` the vectors of `u : Fin n → V` with index at most `m j` span a
  `K`-subspace of dimension greater than `j`, then some subfamily `u ∘ s` with `(s j).val ≤ m j`
  is `K`-linearly independent.
* `LinearIndependent.exists_linearIndependent_comp_finrank_mul`: the packaged corollary the
  roadmap consumes. From `d * k` vectors with `E`-independent images, a `K`-linearly independent
  subfamily of size `k` whose `j`-th member sits among the first `d * j + 1`.

## Implementation notes

The counting half is one dimension count. The `K`-span `S = span K (range u)` has `F`-dimension
`d * finrank K S` by the tower law `Module.finrank_mul_finrank`, so its image under `f` is spanned
over `E` by the `finrank F S` vectors `f (b j)`, `b` an `F`-basis of `S` — the `F`-scalars of an
expansion in `b` act through `E` by the tower `F ⊆ E` — and that `E`-span must accommodate the `#ι`
independent vectors `f (u i)`.

⚠ **The conclusion of the selection half picks members of the family, not combinations of it.**
That is the whole point of the milestone and is why the greedy argument is stated rather than a
dimension count: the chosen vector is `u (s j)` and keeps whatever bound `u (s j)` arrived with,
whereas a `K`-linear combination of lattice vectors has no controlled height. The induction adds
one index at a time, choosing `i ≤ m (last k)` with `u i` outside the span of what is already
selected; such an `i` exists because that span has dimension at most `k`, while the vectors indexed
up to `m (last k)` span more than `k` dimensions by hypothesis.

⚠ **The bound function `m` need not be monotone**, and the selection half knows nothing about `F`,
`E` or `f`: it is a statement about a single field `K`. The tower enters only in the corollary,
where `m j = d * j` and the hypothesis of the selection half is supplied by the counting half
applied to the first `d * j + 1` vectors.

## References

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), §I.3: they pass to
the adèles at exactly this point, because over `𝓞_K` — not a principal ideal domain in general —
one cannot triangularize a sublattice to convert `d * k` vectors independent over `ℝ` into `k`
vectors independent over `K` with the successive minima still controlled. This file is the
replacement for that triangularization: with `F = ℚ`, `K` a number field of degree `d`, `V = Kᴺ`,
`E = ℝ` and `f` the mixed embedding, the corollary yields `y j := u (s j)` independent over `K`
with `s j ≤ d * j`, hence with all archimedean norms at most `λ (d * j + 1)`; since the minima are
nondecreasing, `λ (d * j + 1) ^ d ≤ ∏_{r = 1}^{d} λ (d * j + r)`, so `∏ j, H (y j) ≤ ∏ i, λ i` —
the full product Minkowski's second theorem bounds, with no loss.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition C.2.9 and Theorem 2.9.4: their successive minima count vectors independent over `K`,
which a real convex body cannot see, and this file is the price of that difference.

This is Layer 4.4 of the `ArithmeticHeights` roadmap.
-/
public section
open Module Submodule
section Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end Selection
section RestrictScalars
variable {F K E V W : Type*}
variable [Field F] [Field K] [Field E]
variable [Algebra F K] [Algebra F E] [FiniteDimensional F K]
variable [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V]
variable [AddCommGroup W] [Module F W] [Module E W] [IsScalarTower F E W]

set_option linter.unusedVariables false in
axiom _root_.LinearIndependent.exists_linearIndependent_comp_finrank_mul.{w_u_1,w_u_2,w_u_3,w_u_4,w_u_5} : ∀ {F : Type w_u_1} {K : Type w_u_2} {E : Type w_u_3} {V : Type w_u_4} {W : Type w_u_5}
  [inst : Field F] [inst_1 : Field K] [inst_2 : Field E] [inst_3 : Algebra F K]
  [inst_4 : Algebra F E] [FiniteDimensional F K] [inst_6 : AddCommGroup V] [inst_7 : Module F V]
  [inst_8 : Module K V] [IsScalarTower F K V] [inst_10 : AddCommGroup W] [inst_11 : Module F W]
  [inst_12 : Module E W] [IsScalarTower F E W] (f : V →ₗ[F] W) {k : ℕ}
  {u : Fin (Module.finrank F K * k) → V},
  LinearIndependent E ((⇑f : V → W) ∘ u) →
    ∃ (s : Fin k → Fin (Module.finrank F K * k)),
      LinearIndependent K (u ∘ s) ∧ ∀ (j : Fin k), (↑(s j) : ℕ) ≤ Module.finrank F K * (↑j : ℕ)
end RestrictScalars
end

end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.SuccessiveMinima ====
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
# The successive minima of a symmetric convex body

For a lattice `L` in a finite-dimensional real normed space `E` and a symmetric convex body `B`,
the `i`-th successive minimum is the least dilation of `B` that contains `i + 1` linearly
independent points of `L`. This file defines it, proves it positive, monotone and homogeneous of
degree `-1` in the body, and proves Cassels' Lemma 1: the minima are attained, by one family of
independent lattice vectors realizing all of them at once.

## Main definitions

* `ZLattice.successiveMinimum`: the `i`-th successive minimum, as the infimum of the admissible
  dilations. For `i ≥ finrank ℝ E` there are none and the value is `sInf ∅ = 0`, so every
  statement below carries `i < finrank ℝ E`.

## Main results

* `gauge_le_iff_mem_smul`: the dictionary between Cassels' distance functions and the convex-body
  form pinned by the roadmap. Membership in `t • B` is having gauge at most `t`, for a **closed**
  body; `mem_smul_of_gauge_lt` is the half that needs no closedness.
* `ZLattice.successiveMinimum_pos`: the minima are positive, which is where boundedness of the
  body is used, and `ZLattice.successiveMinimum_eq_zero_of_le`: they vanish above the dimension.
* `ZLattice.successiveMinimum_le_of_le` and `ZLattice.successiveMinimum_smul`: monotone in the
  index, homogeneous of degree `-1` in the body.
* `ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum`: **Cassels' Lemma 1**. There is
  one linearly independent family of lattice vectors whose gauges are the successive minima. This
  is what every later proof consumes; its body form is
  `ZLattice.exists_linearIndependent_mem_smul_successiveMinimum`, which is where closedness of
  the body is used.
* `Finset.prod_pow_le_prod_range`: the regrouping that turns a bound on the product of all `d * k`
  minima into a bound on a product of `k` `d`-th powers — what Layers 5.3 and 5.4 spend to pass
  from the minima of the lattice of a `k`-dimensional `K`-subspace to `k` heights.
* `ZLattice.successiveMinimum_zero_eq`: the zeroth minimum is the least dilation containing a
  nonzero lattice point — the quantity Minkowski's convex-body theorem bounds — and
  `ZLattice.successiveMinimum_zero_le_one` is that theorem read as the case `i = 0`.

## Implementation notes

The body is carried as four separate hypotheses — convex, symmetric, with nonempty interior,
bounded — plus closedness where it is needed, rather than as one bundled structure, so that each
statement says which of them it uses. Cassels indexes the minima by a distance function `F` and
dilates `{x | F x ≤ 1}`; the convex-body form is the pinned one, and `gauge_le_iff_mem_smul` is
the translation, proved once here.

⚠ **Attainment does not need the body to be closed; only its body form does.** The family of
`ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum` realizes the minima as *gauges*
for any bounded symmetric convex body with nonempty interior, and that statement is the one the
proof produces. Turning `gauge B (v j) = λ j` into `v j ∈ λ j • B` is exactly the dictionary, and
exactly what fails for an open body: for the open unit ball no lattice vector lies in `λ 0 • B`
at all, since anything inside that dilation would already have shown a smaller dilation
admissible. The two statements are therefore kept apart, and only the second carries `IsClosed B`.

⚠ **The minima are not monotone in the index without `i < finrank ℝ E`.** Above the dimension
there is no independent family at all, the set of admissible dilations is empty, and the value is
`sInf ∅ = 0`. So `Monotone (successiveMinimum L B)` is false whenever `E` is nontrivial, and a
statement of Minkowski's second theorem that ranged over all of `ℕ` would multiply by zero.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter VIII §1:
the definition, Lemma 1 (attainment) and the elementary properties proved here. E. Bombieri and
W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006), Appendix C.2.
Minkowski's first theorem is Mathlib's
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`.

This is Layer 4.1 of the `ArithmeticHeights` roadmap.
-/
public section
open Metric Module MeasureTheory Set
open scoped Pointwise Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}
/-! ### The body and its gauge

Three facts about a symmetric convex body, none of them about lattices: it is a neighbourhood of
the origin, and its dilations are the sublevel sets of its gauge — from below always, and exactly
when the body is closed. -/

namespace ZLattice
variable {i : ℕ}
/-- The `i`-th **successive minimum** of a set `B` with respect to a lattice `L`: the least
dilation of `B` containing `i + 1` linearly independent points of `L`. The case `i = 0` is the
quantity bounded by Minkowski's convex-body theorem. For `i ≥ finrank ℝ E` there is no such
family and the value is `sInf ∅ = 0`, so every statement about the minima carries
`i < finrank ℝ E`. -/
noncomputable def successiveMinimum (L : Submodule ℤ E) (B : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (i + 1) → E,
    (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v}
variable {L : Submodule ℤ E}

variable [FiniteDimensional ℝ E]
section Elementary
variable [DiscreteTopology L] [IsZLattice ℝ L]

end Elementary
/-- Above the dimension the minima vanish: there is no independent family of `i + 1` vectors at
all, so the set of admissible dilations is empty and its infimum is the junk value `0`. Together
with `successiveMinimum_pos` this is why every statement about the minima is restricted to
`i < finrank ℝ E`. -/
axiom successiveMinimum_eq_zero_of_le (L : Submodule ℤ E) (B : Set E) (hi : finrank ℝ E ≤ i) :
    successiveMinimum L B i = 0
/-- The minima are monotone in the index below the dimension: an independent family of `j + 1`
vectors contains one of `i + 1` vectors, so every dilation admissible at `j` is admissible at
`i`. The hypothesis `j < finrank ℝ E` is not removable — see `successiveMinimum_eq_zero_of_le`. -/
axiom successiveMinimum_le_of_le [DiscreteTopology L] [IsZLattice ℝ L] {j : ℕ} (hij : i ≤ j)
    (hj : j < finrank ℝ E) (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) :
    successiveMinimum L B i ≤ successiveMinimum L B j
section Discrete
variable [DiscreteTopology L]

variable [IsZLattice ℝ L]

/-- **The minima are positive.** A nonzero lattice point has gauge bounded away from zero, so no
small dilation of a bounded body can contain one. -/
axiom successiveMinimum_pos (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) (hi : i < finrank ℝ E) : 0 < successiveMinimum L B i
end Discrete
section Attainment
variable [DiscreteTopology L] [IsZLattice ℝ L]

set_option linter.unusedVariables false in
axiom _root_.ZLattice.exists_linearIndependent_mem_smul_successiveMinimum.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {B : Set E}
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [inst_3 : DiscreteTopology ↥L] [IsZLattice ℝ L],
  Convex ℝ B →
    (∀ x ∈ B, -x ∈ B) →
      (interior B).Nonempty →
        Bornology.IsBounded B →
          IsClosed B →
            ∃ (v : Fin (Module.finrank ℝ E) → E),
              (∀ (j : Fin (Module.finrank ℝ E)), v j ∈ (↑L : Set E)) ∧
                LinearIndependent ℝ v ∧
                  ∀ (j : Fin (Module.finrank ℝ E)),
                    v j ∈ ZLattice.successiveMinimum L B (↑j : ℕ) • B

end Attainment
/-! ### Minkowski's first theorem as the case `i = 0`

The zeroth minimum is the least dilation of the body containing a nonzero lattice point, which is
the quantity Minkowski's convex-body theorem bounds. The identity is measure-free; the bound is
the only statement in this file that mentions a measure. -/

end ZLattice
/-! ### Regrouping a product of minima -/
section Regrouping
set_option linter.unusedVariables false in
axiom _root_.Finset.prod_pow_le_prod_range : ∀ {f : ℕ → ℝ} {N : ℕ},
  (∀ (i : ℕ), 0 ≤ f i) →
    (∀ (i j : ℕ), i ≤ j → j < N → f i ≤ f j) →
      ∀ (d k : ℕ), d * k ≤ N → ∏ j ∈ Finset.range k, f (d * j) ^ d ≤ ∏ i ∈ Finset.range (d * k), f i
end Regrouping
/-! ### Worked examples -/
section Examples
open ZLattice
variable [FiniteDimensional ℝ E] {L : Submodule ℤ E}
end Examples

end
end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.CubeSlicing ====
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
# Vaaler's cube-slicing theorem

**Bombieri–Gubler, Theorem C.3.8 (Vaaler 1979).** Let `Q` be a product of euclidean balls each of
volume one, one factor per block of a partition of the coordinates of `ℝᴺ`. Then every central
slice of `Q` by a linear subspace `V` has volume at least one, the volume being computed on `V`
with its own inner-product structure. Two corollaries: the cube `[-1, 1]ᴺ` has central slices of
volume at least `2 ^ dim V`, and the unit polydisc of `ℂⁿ` has central slices of real volume at
least `2 ^ (dim V / 2)`.

## Main definitions

* `Submodule.prodOrthogonalEquiv V`: the orthogonal decomposition `E ≃ₗ[ℝ] V × Vᗮ`, as a
  measure-preserving linear equivalence.
* `unitBallVolume n`: the volume of the unit ball of `EuclideanSpace ℝ (Fin n)`.

## Main results

* `one_le_volume_subtype_mem`: **Bombieri–Gubler, Theorem C.3.8** in the form the slice bound gives
  it, for an arbitrary measurable convex symmetric `Q` satisfying `HasSliceBound`.
* `one_le_volume_inter_prodBall`: the product-of-balls theorem in the roadmap's form.
* `two_pow_finrank_le_volume_inter_cube`: **Vaaler's cube-slicing theorem**.
* `two_pow_le_volume_inter_polydisc`: the inscribed-cube bound at a complex place.

## Implementation notes

⚠ **The `ε`-thickening needs no dominated convergence, because a slice of a symmetric convex body
is largest at the centre.** Bombieri–Gubler pass to the limit `ε → 0` in
`vol (Q ∩ L_ε) / vol (B_ε)` by computing the limit of the integrand and dominating it. The same
limit is avoided here: the function `z ↦ vol_V {y | y + z ∈ Q}` on `Vᗮ` is log-concave, by Lemma
C.3.4, and even, because `Q` is symmetric, so it is *bounded by its value at zero* — which is the
slice volume being estimated. That turns the right-hand side into
`vol_V (Q ∩ V) * vol (B_ε)` with no limit at all, and the left-hand side is bounded below by
`exp (-π ε ^ 2) * vol (B_ε)` because the Gauss density is. Dividing and letting `ε → 0` is then a
one-line limit of `exp (-π ε ^ 2)`. Brunn's principle — that the central slice is the largest one —
is thus the only extra ingredient, and log-concavity of marginals already supplies it.

⚠ **The complex structure is not needed for the polydisc bound.** The roadmap states
`two_pow_le_volume_inter_polydisc` for a subspace closed under the complex structure `J`, since
that is where the bound is applied; but the proof inscribes the cube of half-side `2 ^ (-1/2)` in
the polydisc and applies the cube case, which gives `√2 ^ dim V`, and `2 ^ (dim V / 2) ≤ √2 ^ dim V`
holds whether or not `dim V` is even. So the hypothesis is dropped here.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem C.3.8; J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific
Journal of Mathematics **83** (1979), 543–553.

This is Layer 4.5 of the `ArithmeticHeights` roadmap.
-/
public section
open MeasureTheory Measure Set ENNReal Pointwise
open scoped Real
section OrthogonalDecomposition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

end OrthogonalDecomposition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Milestones
/-- The volume `ω_n` of the unit ball of `EuclideanSpace ℝ (Fin n)`. -/
@[expose] noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

end Milestones

end
end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.MixedLattice ====
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

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.NumberFieldLattice ====
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
/-- The tuples of algebraic integers, as an `𝓞 K`-submodule of `ι → K`. -/
@[expose] def NumberField.integralTuples (K : Type*) [Field K] (ι : Type*) :
    Submodule (𝓞 K) (ι → K) :=
  Submodule.pi Set.univ fun _ ↦ (1 : Submodule (𝓞 K) K)

/-- The **integral points** `V ∩ (𝓞 K)ⁱ` of a subspace of `Kⁱ`. -/
@[expose] def Submodule.integerPoints (V : Submodule K (ι → K)) : Submodule (𝓞 K) (ι → K) :=
  V.restrictScalars (𝓞 K) ⊓ integralTuples K ι
omit [NumberField K] in
axiom Submodule.mem_integerPoints {V : Submodule K (ι → K)} {x : ι → K} :
    x ∈ V.integerPoints ↔ x ∈ V ∧ ∀ l, ∃ z : 𝓞 K, (z : K) = x l
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

open scoped Classical in
/-- The **real span** of a subspace of `Kⁱ` in the euclidean mixed space of tuples. -/
@[expose] def Submodule.mixedSpan (V : Submodule K (ι → K)) : Submodule ℝ (mixedPi K ι) :=
  Submodule.span ℝ (mixedPiEmb K ι '' (V : Set (ι → K)))

open scoped Classical in
set_option linter.unusedVariables false in
axiom _root_.instFiniteDimensionalMixedSpan.{w_u_1,w_u_2} : ∀ {K : Type w_u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type w_u_2} [Finite ι]
  (V : Submodule K (ι → K)), FiniteDimensional ℝ ↥V.mixedSpan
attribute [instance] _root_.instFiniteDimensionalMixedSpan
open scoped Classical in
/-- The **lattice of integral points** of a subspace, inside its real span: the object whose
covolume the milestone computes. -/
@[expose] def Submodule.mixedLattice (V : Submodule K (ι → K)) : Submodule ℤ ↥V.mixedSpan :=
  Submodule.comap ((V.mixedSpan.subtype).restrictScalars ℤ)
    (Submodule.map (mixedPiEmb K ι) (V.integerPoints.restrictScalars ℤ))
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

open scoped Classical in
set_option linter.unusedVariables false in
axiom _root_.instDiscreteTopologyMixedLattice.{w_u_1,w_u_2} : ∀ {K : Type w_u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type w_u_2} [LinearOrder ι]
  [Finite ι] (V : Submodule K (ι → K)), DiscreteTopology ↥V.mixedLattice
attribute [instance] _root_.instDiscreteTopologyMixedLattice
open scoped Classical in
set_option linter.unusedVariables false in
axiom _root_.instIsZLatticeMixedLattice.{w_u_1,w_u_2} : ∀ {K : Type w_u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type w_u_2} [inst_2 : Fintype ι]
  [inst_3 : LinearOrder ι] [inst_4 : Finite ι] (V : Submodule K (ι → K)),
  IsZLattice ℝ V.mixedLattice
attribute [instance] _root_.instIsZLatticeMixedLattice
open scoped Classical in
/-- **The real span of a subspace of `Kⁱ` has dimension `[K : ℚ] · dim V`.** -/
axiom Submodule.finrank_mixedSpan (V : Submodule K (ι → K)) :
    finrank ℝ ↥V.mixedSpan = finrank ℚ K * finrank K V
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

omit [Finite ι] in
open scoped Classical in
/-- **Membership in the lattice of integral points**, read in `Kⁱ` rather than in the real
span. -/
axiom mem_mixedLattice_iff (V : Submodule K (ι → K)) {y : ↥V.mixedSpan} :
    y ∈ V.mixedLattice ↔ ∃ z ∈ V.integerPoints, mixedPiEmb K ι z = (y : mixedPi K ι)
end NumberField.mixedEmbedding
end
end

end

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v46d2fb14eb8a.ArithmeticHeights.MixedBall ====
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
axiom inner_toMixedPi_toMixedTuple (c c' : mixedIndex K κ → ℝ) :
    inner ℝ (toMixedPi K κ (toMixedTuple K κ c)) (toMixedPi K κ (toMixedTuple K κ c'))
      = ∑ idx, c idx * c' idx
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

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_bb80dd9be488521be413_BombieriVaalerField ====
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
/-- **The height of an integral tuple in a dilate of the body.** -/
axiom arakelovMulHeight_le_of_mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0) (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedBall K ι) :
    arakelovMulHeight x ≤ r ^ finrank ℚ K
section Span
variable [LinearOrder ι] (V : Submodule K (ι → K))
omit [LinearOrder ι] in
open scoped Classical in
axiom convex_preimage_mixedBall :
    Convex ℝ ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)
omit [LinearOrder ι] in
open scoped Classical in
axiom neg_mem_preimage_mixedBall {x : ↥V.mixedSpan}
    (hx : x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) :
    -x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι
omit [LinearOrder ι] in
open scoped Classical in
axiom isClosed_preimage_mixedBall :
    IsClosed ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)
omit [LinearOrder ι] in
open scoped Classical in
axiom isBounded_preimage_mixedBall :
    Bornology.IsBounded ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)
omit [LinearOrder ι] in
open scoped Classical in
axiom interior_preimage_mixedBall_nonempty :
    (interior ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)).Nonempty
open scoped Classical in
set_option linter.unusedVariables false in
axiom _root_.NumberField.mixedEmbedding.prod_successiveMinimum_mixedBall_le.{w_u_1,w_u_2} : ∀ {K : Type w_u_1} [inst : Field K] [inst_1 : NumberField K] {ι : Type w_u_2} [inst_2 : Fintype ι]
  [inst_3 : LinearOrder ι] (V : Submodule K (ι → K)),
  ∏ i ∈ Finset.range (Module.finrank ℚ K * Module.finrank K ↥V),
      ZLattice.successiveMinimum V.mixedLattice
        (Subtype.val ⁻¹' NumberField.mixedEmbedding.mixedBall K ι) i ≤
    (2 ^ Module.finrank K ↥V / unitBallVolume (Module.finrank K ↥V)) ^
          NumberField.InfinitePlace.nrRealPlaces K *
        (2 ^ Module.finrank K ↥V / unitBallVolume (2 * Module.finrank K ↥V)) ^
          NumberField.InfinitePlace.nrComplexPlaces K *
      (√|(↑(NumberField.discr K) : ℝ)| ^ Module.finrank K ↥V * V.arakelovMulHeight)
end Span
end NumberField.mixedEmbedding
namespace NumberField
open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open NumberField.mixedEmbedding
open scoped Pointwise
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
section Main
variable [LinearOrder ι] (V : Submodule K (ι → K))
open scoped Classical in
/-- **Layer 5.3, the relative form.** -/
theorem exists_basis_prod_arakelovMulHeight_le :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, arakelovMulHeight (x l))
        ≤ ((2 : ℝ) ^ finrank K V / unitBallVolume (finrank K V)) ^ nrRealPlaces K
            * ((2 : ℝ) ^ finrank K V / unitBallVolume (2 * finrank K V)) ^ nrComplexPlaces K
            * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
  set B : Set ↥V.mixedSpan := (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι with hB
  have hconv := convex_preimage_mixedBall V
  have hsymm : ∀ z ∈ B, -z ∈ B := fun z hz ↦ neg_mem_preimage_mixedBall V hz
  have hintn := interior_preimage_mixedBall_nonempty V
  have hbdd := isBounded_preimage_mixedBall V
  have hcl := isClosed_preimage_mixedBall V
  obtain ⟨v, hvL, hvind, hvmem⟩ :=
    ZLattice.exists_linearIndependent_mem_smul_successiveMinimum V.mixedLattice hconv hsymm hintn
      hbdd hcl
  have hfr : finrank ℝ ↥V.mixedSpan = finrank ℚ K * finrank K V := V.finrank_mixedSpan
  set e : Fin (finrank ℚ K * finrank K V) ≃ Fin (finrank ℝ ↥V.mixedSpan) := finCongr hfr.symm
    with he
  have hlift : ∀ j, ∃ z ∈ V.integerPoints, mixedPiEmb K ι z = ((v (e j) : mixedPi K ι)) :=
    fun j ↦ (mem_mixedLattice_iff V).1 (hvL (e j))
  choose x hxmem hxemb using hlift
  set fQ : (ι → K) →ₗ[ℚ] mixedPi K ι := (mixedPiEmb K ι).toAddMonoidHom.toRatLinearMap with hfQ
  have hindR : LinearIndependent ℝ (fQ ∘ x) := by
    have h1 : LinearIndependent ℝ (fun j ↦ v (e j)) := hvind.comp e e.injective
    have h2 : LinearIndependent ℝ (fun j ↦ ((v (e j) : mixedPi K ι))) :=
      h1.map' (V.mixedSpan.subtype) (Submodule.ker_subtype _)
    have hfQapp : ∀ z, fQ z = mixedPiEmb K ι z := fun z ↦ rfl
    simpa only [Function.comp_def, hfQapp, hxemb] using h2
  obtain ⟨s, hsind, hsle⟩ :=
    LinearIndependent.exists_linearIndependent_comp_finrank_mul (F := ℚ) (E := ℝ) fQ hindR
  refine ⟨x ∘ s, hsind, fun l ↦ hxmem _, ?_⟩
  set lam : ℕ → ℝ := ZLattice.successiveMinimum V.mixedLattice B with hlam
  have hdpos : 0 < finrank ℚ K := Module.finrank_pos
  have hlampos : ∀ i, i < finrank ℚ K * finrank K V → 0 < lam i := fun i hi ↦
    ZLattice.successiveMinimum_pos V.mixedLattice hconv hsymm hintn hbdd (by rw [hfr]; exact hi)
  have hlamnn : ∀ i, 0 ≤ lam i := by
    intro i
    rcases lt_or_ge i (finrank ℚ K * finrank K V) with h | h
    · exact (hlampos i h).le
    · rw [hlam, ZLattice.successiveMinimum_eq_zero_of_le _ _ (by rw [hfr]; exact h)]
  have hlammono : ∀ i j, i ≤ j → j < finrank ℚ K * finrank K V → lam i ≤ lam j :=
    fun i j hij hj ↦
      ZLattice.successiveMinimum_le_of_le hij (by rw [hfr]; exact hj) hconv hsymm hintn
  have hsmulcoe : ∀ (r : ℝ) (z : ↥V.mixedSpan), z ∈ r • B →
      (z : mixedPi K ι) ∈ r • mixedBall K ι := by
    rintro r z ⟨b, hb, rfl⟩
    exact ⟨(b : mixedPi K ι), hb, by simp⟩
  have hheight : ∀ l : Fin (finrank K V),
      arakelovMulHeight ((x ∘ s) l) ≤ lam (finrank ℚ K * l.val) ^ finrank ℚ K := by
    intro l
    have hsl : (s l).val < finrank ℚ K * finrank K V := (s l).isLt
    have hdl : finrank ℚ K * l.val < finrank ℚ K * finrank K V :=
      (Nat.mul_lt_mul_left hdpos).2 l.isLt
    have hmem : mixedPiEmb K ι (x (s l)) ∈ (lam (s l).val) • mixedBall K ι := by
      have h := hsmulcoe _ _ (hvmem (e (s l)))
      rwa [← hxemb (s l)] at h
    have hintg : ∀ j, ∃ z : 𝓞 K, (z : K) = (x (s l)) j :=
      (Submodule.mem_integerPoints.1 (hxmem (s l))).2
    have h1 : arakelovMulHeight (x (s l)) ≤ (lam (s l).val) ^ finrank ℚ K :=
      arakelovMulHeight_le_of_mem_smul_mixedBall (hlampos _ hsl) (hsind.ne_zero l) hintg hmem
    exact h1.trans (pow_le_pow_left₀ (hlampos _ hsl).le (hlammono _ _ (hsle l) hdl) _)
  calc (∏ l, arakelovMulHeight ((x ∘ s) l))
      ≤ ∏ l : Fin (finrank K V), lam (finrank ℚ K * l.val) ^ finrank ℚ K :=
        Finset.prod_le_prod₀ (fun l _ ↦ (arakelovMulHeight_pos _).le) fun l _ ↦ hheight l
    _ = ∏ j ∈ Finset.range (finrank K V), lam (finrank ℚ K * j) ^ finrank ℚ K :=
        Fin.prod_univ_eq_prod_range (fun i ↦ lam (finrank ℚ K * i) ^ finrank ℚ K) _
    _ ≤ ∏ i ∈ Finset.range (finrank ℚ K * finrank K V), lam i :=
        Finset.prod_pow_le_prod_range hlamnn hlammono _ _ le_rfl
    _ ≤ _ := prod_successiveMinimum_mixedBall_le V
end Main
section Kernel
variable [LinearOrder ι] {m : ℕ}
end Kernel
end NumberField
