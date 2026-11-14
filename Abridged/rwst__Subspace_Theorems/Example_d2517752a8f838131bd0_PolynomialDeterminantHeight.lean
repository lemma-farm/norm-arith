module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_d2517752a8f838131bd0_PolynomialDeterminantHeight ====
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The height of a determinant of polynomials

The polynomial Roth's lemma runs on is the determinant of a `p × p` matrix whose entries are
Hasse derivatives of one polynomial `P`. Its height has to be bounded by `p` times the height of
`P` plus a constant, and there is no projective bound on the height of a *sum* of polynomials
that could be applied term by term to the Leibniz expansion: `H(N X + 1)` is `N` while both
summands have height `1`. The estimate has to be made at each absolute value and transported
once, which is what `Finsupp.mulHeight_le_pow_of_forall_iSup_le` is for.

Locally there is nothing to it. A product of `n` polynomials costs one factor
`#(support)` per multiplication at an archimedean absolute value — Gelfond's local estimate with
the *smaller* support, so that the constant stays `B ^ n` and does not grow quadratically with
`n` — and nothing at all at a nonarchimedean one, by Gauss's lemma. A sum of `n!` terms costs
`n!` at an archimedean absolute value and nothing at a nonarchimedean one.

## Main results

* `MvPolynomial.iSup_coeff_prod_le` and
  `MvPolynomial.iSup_coeff_prod_le_of_isNonarchimedean`: the local factor of a finite product.
* `MvPolynomial.iSup_coeff_sum_le` and `MvPolynomial.iSup_coeff_sum_le_of_isNonarchimedean`:
  the local factor of a finite sum.
* `MvPolynomial.iSup_coeff_det_le` and `MvPolynomial.iSup_coeff_det_le_of_isNonarchimedean`:
  the local factor of a determinant.
* `MvPolynomial.mulHeight_det_le`: the height of a determinant of polynomials whose local
  factors are bounded against those of one polynomial `P`.
* `MvPolynomial.card_support_le_prod` and `MvPolynomial.card_support_le_two_pow`: a polynomial
  of partial degrees at most `d` has at most `∏ j, (d j + 1) ≤ 2 ^ ∑ j, d j` monomials.

## Implementation notes

⚠ **The support count, not the total degree, is what keeps the constant linear in `n`.**
`MvPolynomial.iSup_coeff_mul_le_two_pow` charges `2 ^ (totalDegree p + totalDegree q)`, and the
accumulated product in a `n`-fold product has total degree `n` times the individual one, so
iterating it costs `2 ^ (D n (n+1) / 2)`. `MvPolynomial.iSup_coeff_mul_le_card_support` charges
the *minimum* of the two support counts, which is always the new factor's, so iterating it costs
`B ^ n` with `B` a bound on one factor's support. In Roth's lemma `n` is the number of columns
and can be as large as the smallest degree, so the difference is the whole estimate.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 1.6.11 and Lemma 6.3.7.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/
@[expose] public section
open Finset Height AdmissibleAbsValues
namespace MvPolynomial
/-! ### Counting the monomials in a box -/
section Support
variable {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]

end Support
/-! ### Local estimates for sums and products -/
section Local
variable {K : Type*} [Field K] {σ ι : Type*} {v : AbsoluteValue K ℝ}


set_option linter.unusedVariables false in
/-- **The local factor of a finite product at a nonarchimedean absolute value**, by Gauss's
lemma, with no constant. -/
theorem iSup_coeff_prod_le_of_isNonarchimedean (hv : IsNonarchimedean v) (s : Finset ι)
    (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) 
    (h_MvPolynomial_iSup_coeff_one : ∀ {K : Type u_1} [inst : Field K] {σ : Type u_2} (v : AbsoluteValue K ℝ),
      ⨆ (ν : σ →₀ ℕ), (v : K → ℝ) ((AddMonoidAlgebra.coeff 1 : (σ →₀ ℕ) → K) ν) = 1)
    (h_MvPolynomial_iSup_coeff_nonneg : ∀ {K : Type u_1} [inst : Field K] {σ : Type u_2} (P : MvPolynomial σ K) (v : AbsoluteValue K ℝ),
      0 ≤ ⨆ (ν : σ →₀ ℕ), (v : K → ℝ) ((P.coeff : (σ →₀ ℕ) → K) ν))
    (h_MvPolynomial_iSup_coeff_mul : ∀ {K : Type u_1} [inst : Field K] {σ : Type u_2} {v : AbsoluteValue K ℝ},
      IsNonarchimedean (⇑v : K → ℝ) →
        ∀ (p q : MvPolynomial σ K),
          ⨆ (m : σ →₀ ℕ), (v : K → ℝ) (((p * q).coeff : (σ →₀ ℕ) → K) m) =
            (⨆ (m : σ →₀ ℕ), (v : K → ℝ) ((p.coeff : (σ →₀ ℕ) → K) m)) *
              ⨆ (m : σ →₀ ℕ), (v : K → ℝ) ((q.coeff : (σ →₀ ℕ) → K) m))
    :
    (⨆ ν, v ((∏ a ∈ s, f a).coeff ν)) ≤ C ^ #s := by
  classical
  induction s using Finset.induction with
  | empty => simpa using le_of_eq (h_MvPolynomial_iSup_coeff_one v)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ',
        h_MvPolynomial_iSup_coeff_mul hv]
      exact mul_le_mul (hf a (Finset.mem_insert_self a s))
        (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) (h_MvPolynomial_iSup_coeff_nonneg _ v) hC

end Local
/-! ### The determinant -/
section Det
variable {K : Type*} [Field K] {σ : Type*} {v : AbsoluteValue K ℝ} {n : ℕ}

variable [AdmissibleAbsValues K]

end Det
end MvPolynomial
