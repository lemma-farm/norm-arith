/-
# Algebraic support for the Crouzeix--Palencia product bound

This file proves the polynomial resolvent splitting used in L4.2e.  Dividing
`p` by `X - z` gives

`p = C (p.eval z) + (X - C z) * (p /ₘ (X - C z))`.

After evaluation at an operator and left multiplication by the resolvent, the
second term collapses using `R_A(z) (zI - A) = I`.  The result separates the
scalar boundary value from a polynomial term, which is the algebraic input to
the product estimate.

## Main declaration

* `resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic` -- the
  resolvent splitting identity.
* `aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic` -- its
  right-oriented form, matching the product `p(A) G` in L4.2e.
* `aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic` --
  the scalar-boundary-weighted pointwise integrand identity.
* `commute_aeval_resolvent` -- polynomial evaluation commutes with the
  resolvent wherever it is defined.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral` -- pulls
  polynomial evaluation through the auxiliary contour integral.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split` -- rewrites that
  contour integral using the pointwise resolvent splitting.
* `commute_aeval_crouzeixPolynomialAuxiliaryOperator` -- polynomial
  evaluation commutes with every polynomial auxiliary contour operator.
* `crouzeixPolynomialAuxiliaryOperator_smul` -- the auxiliary operator is
  conjugate-linear in its polynomial argument.
* `polynomial_auxiliary_bounds_of_normalized` -- transfers both sharp bounds
  from unit sup norm to every polynomial with positive sup norm.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.AuxOperator
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.SpectralSet.Basic
import Mathlib
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    resolvent A z * Polynomial.aeval A p =
      Polynomial.eval z p • resolvent A z -
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C z)
  have hpoly : Polynomial.C (Polynomial.eval z p) +
      (Polynomial.X - Polynomial.C z) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p z]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C z)
  have hres : resolvent A z * (algebraMap ℂ (E →L[ℂ] E) z - A) = 1 := by
    calc
      resolvent A z * (algebraMap ℂ (E →L[ℂ] E) z - A) =
          (↑hz.unit⁻¹ : E →L[ℂ] E) * ↑hz.unit := by
        rw [spectrum.resolvent_eq hz, hz.unit_spec]
      _ = 1 := Units.inv_mul _
  conv_lhs => rhs; rw [← hpoly]
  simp only [map_add, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X, mul_add,
    ← mul_assoc]
  rw [show A - algebraMap ℂ (E →L[ℂ] E) z =
      -(algebraMap ℂ (E →L[ℂ] E) z - A) by abel]
  rw [mul_neg, hres, neg_mul, one_mul]
  simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, q, sub_eq_add_neg]
/-- The right-oriented resolvent splitting used directly in `p(A) G`:
`p(A) R_A(z) = p(z) R_A(z) - (p /ₘ (X - z))(A)`. -/
theorem aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    Polynomial.aeval A p * resolvent A z =
      Polynomial.eval z p • resolvent A z -
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C z)
  have hpoly : Polynomial.C (Polynomial.eval z p) +
      q * (Polynomial.X - Polynomial.C z) = p := by
    rw [mul_comm]
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p z]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C z)
  have hres : (algebraMap ℂ (E →L[ℂ] E) z - A) * resolvent A z = 1 := by
    calc
      (algebraMap ℂ (E →L[ℂ] E) z - A) * resolvent A z =
          (↑hz.unit : E →L[ℂ] E) * ↑hz.unit⁻¹ := by
        rw [spectrum.resolvent_eq hz, hz.unit_spec]
      _ = 1 := Units.mul_inv _
  conv_lhs => lhs; rw [← hpoly]
  simp only [map_add, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X, add_mul,
    mul_assoc]
  rw [show A - algebraMap ℂ (E →L[ℂ] E) z =
      -(algebraMap ℂ (E →L[ℂ] E) z - A) by abel]
  rw [neg_mul, mul_neg, hres, mul_one]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, q, sub_eq_add_neg]
/-- The right-oriented splitting with a scalar boundary weight `h`, in the
pointwise form used before applying contour-integral linearity in L4.2e. -/
theorem aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) (h : ℂ) :
    Polynomial.aeval A p * (h • resolvent A z) =
      (h * Polynomial.eval z p) • resolvent A z -
        h • Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by
  rw [mul_smul_comm,
    aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic A p hz]
  simp only [smul_sub, smul_smul]
/-- Polynomial evaluation at `A` commutes with the resolvent of `A`. -/
theorem commute_aeval_resolvent (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) : Commute (Polynomial.aeval A p) (resolvent A z) := by
  rw [Commute]
  exact
    (aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic A p hz).trans
      (resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic A p hz).symm
section AuxiliaryContour
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
/-- Polynomial evaluation at `A` pulls through the normalized auxiliary
contour integral. -/
theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => Polynomial.aeval A p *
            (star (Polynomial.eval z p) • resolvent A z))
          Omega.boundaryParam := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  rw [mul_smul_comm]
  rw [← contourIntegral_const_mul (Polynomial.aeval A p)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega p hOmega)]
/-- After pulling `p(A)` through the auxiliary contour integral, the
pointwise resolvent splitting separates the squared boundary value from the
polynomial divided-difference term. -/
theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z =>
            (star (Polynomial.eval z p) * Polynomial.eval z p) • resolvent A z -
              star (Polynomial.eval z p) •
                Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral A Omega p hOmega]
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg (fun Q : H →L[ℂ] H => deriv Omega.boundaryParam t • Q)
  exact aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
    A p (Omega.boundaryParam_mem_resolventSet A hOmega t)
      (star (Polynomial.eval (Omega.boundaryParam t) p))
/-- Polynomial evaluation at `A` commutes with every polynomial auxiliary
contour operator whose boundary lies in the resolvent set of `A`. -/
theorem commute_aeval_crouzeixPolynomialAuxiliaryOperator
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Commute (Polynomial.aeval A p)
      (crouzeixPolynomialAuxiliaryOperator A Omega q) := by
  rw [Commute]
  change Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega q =
    crouzeixPolynomialAuxiliaryOperator A Omega q * Polynomial.aeval A p
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  rw [mul_smul_comm, smul_mul_assoc]
  rw [← contourIntegral_const_mul (Polynomial.aeval A p)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega q hOmega)]
  rw [← contourIntegral_mul_const (Polynomial.aeval A p)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega q hOmega)]
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg (fun Q : H →L[ℂ] H => deriv Omega.boundaryParam t • Q)
  change Polynomial.aeval A p *
      (star (Polynomial.eval (Omega.boundaryParam t) q) •
        resolvent A (Omega.boundaryParam t)) =
    (star (Polynomial.eval (Omega.boundaryParam t) q) •
        resolvent A (Omega.boundaryParam t)) * Polynomial.aeval A p
  rw [mul_smul_comm, smul_mul_assoc]
  apply congrArg (fun Q : H →L[ℂ] H =>
    star (Polynomial.eval (Omega.boundaryParam t) q) • Q)
  exact (commute_aeval_resolvent A p
    (Omega.boundaryParam_mem_resolventSet A hOmega t)).eq
end AuxiliaryContour
section AuxiliaryHomogeneity
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
end AuxiliaryHomogeneity
