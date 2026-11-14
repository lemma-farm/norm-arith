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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Sum.Order
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Fintype.Order
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Nat.Choose.Bounds

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.DiophantineApproximation.MultiHomogeneous ====
public section
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
-- Used only inside proofs.
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Multihomogeneous polynomials and the substitution by linear forms

The Subspace Theorem's auxiliary polynomial lives on a product of projective spaces: it is
multihomogeneous of degree `d h` in each of `m` blocks `X h : ι → K` of `n + 1` variables, and
what is read off it is its expansion in the monomials

`∏ h, ∏ i, (L v i (X h)) ^ (J h i)`

in a system of independent linear forms `L v` attached to a place `v`. This file builds that
machinery over an arbitrary commutative ring: the multidegree, the block substitution, and the
one fact about Hasse derivatives that the vanishing statement of Layer 5.2 needs.

The block substitution is `X (h, j) ↦ ∑ i, A j i • X (h, i)`, the same change of coordinates in
every block, and the expansion coefficients `a(L; J; I)` of Bombieri–Gubler 7.5.14 are the
coefficients of `blockSubst A⁻¹ (hasseDeriv I P)`, with `A` the matrix of the forms.

## Main definitions

* `MvPolynomial.IsMultiHomogeneous`: multihomogeneity of multidegree `d : κ → ℕ` for a polynomial
  in the variables `κ × ι`.
* `MvPolynomial.blockSubst`: the block-wise linear substitution, as an algebra map.
* `MvPolynomial.multiMons`: the monomials of multidegree `d`, the coefficient space of `P(d)`.
* `MvPolynomial.ofMulti`: the polynomial named by a coefficient vector on `multiMons d`.

## Main results

* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`: **the key vanishing statement** — a
  coefficient of the expansion of `∂_I P` vanishes as soon as the coefficients of `P` vanish at
  all the orders `J + I'` with `I'` of the same block degrees as `I`.
* `MvPolynomial.pderiv_blockSubst`: the chain rule for the block substitution, which is what that
  statement is proved from.
* `MvPolynomial.blockSubst_coeff_mem_of_row`: if a row of the substitution is a unit vector, an
  upward closed condition on the exponents along one coordinate passes to another; so the
  vanishing conditions of Layer 5.2 depend on a form, not on the system it sits in.
* `MvPolynomial.IsMultiHomogeneous.blockSubst`: a linear change of coordinates inside the blocks
  preserves the multidegree.
* `MvPolynomial.IsMultiHomogeneous.hasseDeriv`: a Hasse derivative of order `I` is
  multihomogeneous of multidegree `d h - ∑ i, I (h, i)` — the block degrees drop separately, which
  is what the upper half of Lemma 7.5.15 is read off.
* `MvPolynomial.IsWeightedHomogeneous.aeval`: the general statement behind it — a substitution
  that respects the weights preserves weighted homogeneity.
* `MvPolynomial.card_multiMons`, `MvPolynomial.card_multiMons_le` and
  `MvPolynomial.multiMons_nonempty`: the count of the monomials of multidegree `d`, exactly as a
  product over the blocks and crudely as `∏ t : κ × ι, (d t.1 + 1)`.
* `MvPolynomial.coeff_blockSubst_ofMulti`: the coefficient of a substituted auxiliary polynomial
  as a linear form in the unknowns, which is the row of the condition matrix of Layer 5.2.

## Implementation notes

⚠ **Multihomogeneity is Mathlib's weighted homogeneity for the weight `Pi.single h 1`**, and
`MvPolynomial.isMultiHomogeneous_iff` is the dictionary. The predicate is stated separately
because every user reads it as "degree `d h` in the `h`-th block", which is a `Finset.sum` over
`ι` rather than a `Finsupp.weight`; the closure properties are imported through the dictionary.

⚠ **The chain rule is what makes the vanishing statement true, and it is not the trivial one.**
Bombieri–Gubler differentiate in the *original* coordinates and expand in the *transformed* ones,
so `a(L; J; I)` is not `binom(J + I, I) · a(L; J + I; 0)`: it is a combination of those
coefficients over all orders `I'` with the same block degrees as `I`, because `∂ / ∂x (h, k)` is
the combination `∑ i, A i k ∂ / ∂y (h, i)`. The proof below is an induction on the order of the
derivative that never names the combination: one derivative is peeled off with
`MvPolynomial.hasseDeriv_comp`, the chain rule turns it into a sum over the block, and the
inductive hypothesis is applied to each summand. The constant `hasseDeriv_comp` produces is a
positive natural number, which is why the field has to have characteristic zero.

⚠ **The monomials of multidegree `d` are indexed by a `Finset`, not a subtype**, so that they
carry a `Fintype` instance without a decidability argument and so that
`MvPolynomial.card_multiMons` hands the counting of Layer 5.2 straight to
`Fintype.piFinset`, which is where the deviation estimate of
`DiophantineApproximation/MonomialDeviation.lean` counts.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.14.

This is part of Layer 5.2 of the `DiophantineApproximation` roadmap.
-/
@[expose] public section
open Finset
namespace MvPolynomial
variable {κ ι R : Type*} [CommRing R] [Fintype ι]

section Weight
variable [Finite κ] [DecidableEq κ]

end Weight
/-! ### Weighted homogeneity under a substitution -/
section Aeval
variable {σ M : Type*} [AddCommMonoid M] {w : σ → M}

end Aeval
/-! ### The block substitution -/
section BlockSubst
/-- The **block-wise linear substitution** `X (h, j) ↦ ∑ i, A j i • X (h, i)`: the same change of
coordinates in every block. -/
noncomputable def blockSubst (A : Matrix ι ι R) :
    MvPolynomial (κ × ι) R →ₐ[R] MvPolynomial (κ × ι) R :=
  aeval fun p : κ × ι ↦ ∑ i, C (A p.2 i) * X (p.1, i)

variable [DecidableEq ι]

end BlockSubst
/-! ### The chain rule -/
section ChainRule

end ChainRule
/-! ### Vanishing of the expansion coefficients -/
section Vanishing
variable [DecidableEq κ]

variable {K : Type*} [Field K] [CharZero K] [DecidableEq ι] [Fintype κ]

end Vanishing
/-! ### The monomials of a fixed multidegree -/
section Monomials

section TotalDegree
variable [Fintype κ]

end TotalDegree
variable [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end Monomials
/-! ### The coefficient vector of a multihomogeneous polynomial -/
section OfMulti
variable {K : Type*} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {d : κ → ℕ}

end OfMulti
end MvPolynomial

end
end

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_d64286467356b6054a9a_SubspaceAuxiliary ====
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
# The multihomogeneous auxiliary polynomial

Step I of the proof of the Subspace Theorem builds one polynomial in `m` blocks of `n + 1`
variables that vanishes, to high order in every block, along every one of the finitely many
systems of linear forms in play. This file is that construction: Bombieri–Gubler's (7.5.14) and
Lemma 7.5.15.

The space of candidates is the multihomogeneous polynomials of a fixed multidegree `d : κ → ℕ`,
whose monomials are `MvPolynomial.multiMons d` (`DiophantineApproximation.MultiHomogeneous`). For
one invertible matrix `A` the polynomial read in the coordinates `A · X h` is
`MvPolynomial.blockSubst A⁻¹ P`, and the expansion coefficients of the Hasse derivatives that
Lemma 7.5.15 is about are the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)`.

Three things have to be supplied. *That enough coefficients may be killed*: the monomials whose
exponent of one variable is far below its mean `∑ h, d h / (n + 1)` are exponentially few
(`DiophantineApproximation.MonomialDeviation`), so the conditions are at most half as many as the
unknowns and Siegel's lemma applies. *That the height stays linear in `∑ h, d h`*: the height of
the condition matrix and of a substituted Hasse derivative are controlled here from the local
factors, the only inputs being the number of monomials, the number of variables in a block, and
one reference tuple collecting the entries of all the matrices. *That killing those coefficients
kills the others*: the vanishing propagates from order `0` to order `I` by the chain rule, which
is `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`.

## Main results

* `Height.mulHeight_le_pow_mul_mul_pow` and `Height.mulHeight_le_pow_mul_pow`: **transport from
  local factors to the height** — a tuple whose local factor is at most `C` times a product of a
  local factor of `z` and a `D`-th power of one of `y` at the archimedean absolute values, and at
  most that product at the nonarchimedean ones, has height at most
  `C ^ totalWeight K * H z * H y ^ D`.
* `MvPolynomial.iSup_coeff_blockSubst_le` and
  `MvPolynomial.iSup_coeff_blockSubst_le_of_isNonarchimedean`: **the local factor of a substituted
  polynomial**, with `#support · (#ι · ‖A‖_v) ^ D` at an archimedean absolute value and
  `‖A‖_v ^ D` at a nonarchimedean one (Gauss's lemma).
* `MvPolynomial.mulHeight_blockSubst_hasseDeriv_le` and its logarithmic form
  `MvPolynomial.logHeight_blockSubst_hasseDeriv_le`: **the height of a substituted Hasse
  derivative**.
* `MvPolynomial.mulHeight_matrix_blockSubst_monomial_le`: **the height of the condition matrix**,
  which does not depend on the number of rows or columns.
* `MvPolynomial.mulHeight_eq_mulHeight_coeff_multiMons` and
  `MvPolynomial.absMulHeight_coeff_multiMons`: the dictionary between the vector Siegel's lemma
  produces and the polynomial the milestone is about.
* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero`: **Siegel's lemma in
  the multihomogeneous setting** — at most half as many linear conditions as monomials give a
  nonzero multihomogeneous solution of logarithmic height `O (∑ h, d h)`.
* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero`:
  **the milestone**, Lemma 7.5.15.

## Implementation notes

⚠ **The chain rule is the whole content of the vanishing statement.** The expansion coefficient
`a(L v; J; I)` is *not* `binom (J + I) I · a(L v; J + I; 0)`: Bombieri–Gubler differentiate in the
original coordinates and expand in the transformed ones, so a coefficient of `∂_I P` is a
combination, over all orders with the same block degrees, of coefficients of `P` read in the
transformed coordinates. `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` proves exactly what is
needed by induction on the order and never names that combination. It needs characteristic zero,
because `hasseDeriv_comp` produces a positive integer factor that has to be inverted.

⚠ **The conditions imposed are at order `0` only, and they are indexed by the monomial.** For each
form, that is each row `i` of some `A v` up to equality, and each monomial `N` of multidegree `d`
with `∑ h, N (h, i) / d h ≤ m/(n+1) − m η`, the condition is `(blockSubst (A v)⁻¹ P).coeff N = 0`.
That
this implies the vanishing at every order `I` with `∑ h, (∑ i, I (h, i)) / d h ≤ m η` and every
`J` with `∑ h, J (h, i) / d h ≤ m/(n+1) − 2 m η` is exactly where the factor `2` in the book's
`2 m η` is spent: `N = J + I'` moves the threshold by at most `m η`.

⚠ **The conditions are counted by forms, not by places** (Evertse–Schlickewei's construction from
the distinct forms). Whether all monomials of `P` read in the coordinates `A v` have large
exponent along the row `i` depends on that row alone: another system with the same form in row
`i'` differs by a substitution whose row `i'` is a unit vector
(`MvPolynomial.blockSubst_coeff_mem_of_row`). So one family of conditions per distinct form `F`
suffices, and the count is `2 #F` where Bombieri–Gubler have `2 (n + 1) |S|`.

⚠ **The upper half of the book's interval is free.** A Hasse derivative of a multihomogeneous
polynomial is multihomogeneous (`MvPolynomial.IsMultiHomogeneous.hasseDeriv`), so a nonzero
coefficient has `∑ i, ∑ h, J (h, i) / d h = m − ∑ h, (∑ i, I (h, i)) / d h`. If one exponent
exceeds `m/(n+1) + 2 n m η`, the remaining `n` of them average below `m/(n+1) − 2 m η`, and the
lower half applies to one of those. This is why `n ≥ 1` is needed a second time.

⚠ **The hypothesis on `m` is strict here.** Bombieri–Gubler ask
`m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)` (here `4 log (2 #F) / ((n+1)(n+2) η²)`), which
leaves no room for the error term `(η (n+1)(n+2)/2)² / (2(n+1)) · ∑ h, 1/d h` of the Chernoff
bound; that term is positive for every `d` and tends to `0` only as `d → ∞`. The strict
inequality creates a positive slack, and `D₀` is chosen to make the error term smaller than it.
Replacing `2 #F` by `4 #F` and keeping `≥` would do the same.

⚠ **`C₂` and `C₃` are allowed to depend on `m`, `S` and `η`.** The book claims they depend only on
`K` and the forms. That is true — the `m`-dependence sits in `log #multiMons d`, which is
`O (log d)` and could be absorbed into `D₀` — but Layer 5.6 fixes `m` before it uses `C₂`, so
nothing downstream needs the stronger form, and the crude bound
`log #multiMons d ≤ #ι · ∑ h, d h` keeps the proof linear.

⚠ **Mathlib's finiteness of the nonarchimedean local factors is private.** `Height.mulHeight` is
built from a `finprod` over the nonarchimedean absolute values, and the fact that the local factors
of a nonzero tuple differ from `1` at only finitely many of them is proved in Mathlib as a
`private lemma`. It is reproved here as `Height.hasFiniteMulSupport_iSup`; `fun_prop` cannot be
used for it across the module boundary, because it would have to name the private lemma.

⚠ **Only the `≤` direction of the height transport is available.** Mathlib's
`Finsupp.mulHeight_le_of_forall_iSup_le` needs *equality* of the local factors at the
nonarchimedean absolute values. The archimedean product and the nonarchimedean `finprod` are
therefore compared separately here (`finprod_le_finprod₀`, `finprod_pow`, `finprod_mul_distrib`).

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
(7.5.14), Lemma 7.5.15 and (7.20)–(7.25).

This is Layer 5.2 of the `DiophantineApproximation` roadmap.
-/
@[expose] public section
open Finset Height AdmissibleAbsValues Real
namespace Height
variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ρ : Type*} [Finite ι] [Finite ρ]

end Height
namespace MvPolynomial
variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-! ### The local factor of a substituted polynomial -/

omit [DecidableEq ι] [DecidableEq κ] in
set_option linter.unusedVariables false in
/-- **The local factor of a substituted polynomial**, nonarchimedean form: neither the number of
monomials nor the number of variables appears. -/
theorem iSup_coeff_blockSubst_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (M : Matrix ι ι K)
    {R : MvPolynomial (κ × ι) K} {D : ℕ} (hR : ∀ ν ∈ R.support, ∑ t, ν t ≤ D) 
    (h_MvPolynomial_iSup_coeff_blockSubst_monomial_le_of : ∀ {K : Type u_1} [inst : Field K] {κ : Type u_2} {ι : Type u_3} [inst_1 : Fintype ι]
      [inst_2 : Fintype κ] (v : AbsoluteValue K ℝ) (A : Matrix ι ι K) {c : ℝ},
      1 ≤ c →
        (∀ (p : MvPolynomial (κ × ι) K) (t : κ × ι),
            ⨆ (m : κ × ι →₀ ℕ),
                (v : K → ℝ)
                  (((p *
                          (MvPolynomial.blockSubst A : MvPolynomial (κ × ι) K → MvPolynomial (κ × ι) K)
                            (MvPolynomial.X t)).coeff :
                      (κ × ι →₀ ℕ) → K)
                    m) ≤
              c *
                ((⨆ (m : κ × ι →₀ ℕ), (v : K → ℝ) ((p.coeff : (κ × ι →₀ ℕ) → K) m)) *
                  ⨆ (m : κ × ι →₀ ℕ),
                    (v : K → ℝ)
                      ((((MvPolynomial.blockSubst A : MvPolynomial (κ × ι) K → MvPolynomial (κ × ι) K)
                              (MvPolynomial.X t)).coeff :
                          (κ × ι →₀ ℕ) → K)
                        m))) →
          ∀ (N : ℕ) (ν : κ × ι →₀ ℕ),
            ∑ t : κ × ι, (ν : κ × ι → ℕ) t = N →
              ⨆ (J : κ × ι →₀ ℕ),
                  (v : K → ℝ)
                    ((((MvPolynomial.blockSubst A : MvPolynomial (κ × ι) K → MvPolynomial (κ × ι) K)
                            ((MvPolynomial.monomial ν : K → MvPolynomial (κ × ι) K) 1)).coeff :
                        (κ × ι →₀ ℕ) → K)
                      J) ≤
                (c * Max.max (⨆ (p : ι × ι), (v : K → ℝ) (A p.1 p.2)) 1) ^ N)
    (h_MvPolynomial_iSup_coeff_sum_le_of_isNonarchimedean : ∀ {K : Type u_1} [inst : Field K] {σ ι : Type (max u_2 u_3)} {v : AbsoluteValue K ℝ},
      IsNonarchimedean (⇑v : K → ℝ) →
        ∀ (s : Finset ι) (f : ι → MvPolynomial σ K) {C : ℝ},
          0 ≤ C →
            (∀ a ∈ s, ⨆ (ν : σ →₀ ℕ), (v : K → ℝ) (((f a).coeff : (σ →₀ ℕ) → K) ν) ≤ C) →
              ⨆ (ν : σ →₀ ℕ), (v : K → ℝ) (((∑ a ∈ s, f a).coeff : (σ →₀ ℕ) → K) ν) ≤ C)
    (h_Finsupp_bddAbove_range_apply : ∀ {K : Type u_1} [inst : Field K] {α : Type (max u_2 u_3)} (x : α →₀ K) (v : AbsoluteValue K ℝ),
      BddAbove (Set.range fun (i : α) ↦ (v : K → ℝ) ((x : α → K) i)))
    (h_MvPolynomial_blockSubst_eq_sum : ∀ {K : Type u_1} [inst : Field K] {κ : Type u_2} {ι : Type u_3} [inst_1 : Fintype ι]
      (M : Matrix ι ι K) (R : MvPolynomial (κ × ι) K),
      (MvPolynomial.blockSubst M : MvPolynomial (κ × ι) K → MvPolynomial (κ × ι) K) R =
        ∑ ν ∈ R.support,
          (MvPolynomial.C : K → MvPolynomial (κ × ι) K) ((R.coeff : (κ × ι →₀ ℕ) → K) ν) *
            (MvPolynomial.blockSubst M : MvPolynomial (κ × ι) K → MvPolynomial (κ × ι) K)
              ((MvPolynomial.monomial ν : K → MvPolynomial (κ × ι) K) 1))
    (h_MvPolynomial_iSup_coeff_mul : ∀ {K : Type u_1} [inst : Field K] {σ : Type (max u_2 u_3)} {v : AbsoluteValue K ℝ},
      IsNonarchimedean (⇑v : K → ℝ) →
        ∀ (p q : MvPolynomial σ K),
          ⨆ (m : σ →₀ ℕ), (v : K → ℝ) (((p * q).coeff : (σ →₀ ℕ) → K) m) =
            (⨆ (m : σ →₀ ℕ), (v : K → ℝ) ((p.coeff : (σ →₀ ℕ) → K) m)) *
              ⨆ (m : σ →₀ ℕ), (v : K → ℝ) ((q.coeff : (σ →₀ ℕ) → K) m))
    (h_MvPolynomial_iSup_coeff_C_mul_le : ∀ {K : Type u_1} [inst : Field K] {κ : Type u_2} {ι : Type u_3} (v : AbsoluteValue K ℝ) (a : K)
      (Q : MvPolynomial (κ × ι) K),
      ⨆ (m : κ × ι →₀ ℕ),
          (v : K → ℝ)
            ((((MvPolynomial.C : K → MvPolynomial (κ × ι) K) a * Q).coeff : (κ × ι →₀ ℕ) → K) m) ≤
        (v : K → ℝ) a * ⨆ (m : κ × ι →₀ ℕ), (v : K → ℝ) ((Q.coeff : (κ × ι →₀ ℕ) → K) m))
    :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst M R).coeff m))
      ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ D := by
  have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_sup_right
  have hmul : ∀ (p : MvPolynomial (κ × ι) K) (t : κ × ι),
      (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst M (X t)).coeff m))
        ≤ 1 * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
            * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst M (X t)).coeff m)) := by
    intro p t
    rw [one_mul, h_MvPolynomial_iSup_coeff_mul hv]
  have hmono : ∀ ν ∈ R.support,
      (⨆ m : κ × ι →₀ ℕ, v ((C (R.coeff ν) * blockSubst M (monomial ν (1 : K))).coeff m))
        ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ D := by
    intro ν hν
    refine (h_MvPolynomial_iSup_coeff_C_mul_le v _ _).trans ?_
    refine mul_le_mul (le_ciSup (h_Finsupp_bddAbove_range_apply R.coeff v) ν) ?_
      (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    have hmon := h_MvPolynomial_iSup_coeff_blockSubst_monomial_le_of v M le_rfl hmul (∑ t, ν t) ν rfl
    rw [one_mul] at hmon
    exact hmon.trans (pow_le_pow_right₀ hB1 (hR ν hν))
  rw [h_MvPolynomial_blockSubst_eq_sum]
  exact h_MvPolynomial_iSup_coeff_sum_le_of_isNonarchimedean hv R.support _
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (pow_nonneg (by linarith) D)) hmono
/-! ### From local factors to the height of a polynomial -/
section Heights
end Heights
section Dictionary
end Dictionary
section Absolute
end Absolute
section Siegel
end Siegel
section Counting
end Counting
section Milestone
end Milestone
section Acceptance
end Acceptance
end MvPolynomial
