/-
# General smooth-domain symmetrized auxiliary bound

This file assembles the sharp L4.2d estimate on a smooth boundary once the
three genuinely analytic/geometric inputs are available:

* the polynomial and resolvent Cauchy identities for the parametrized curve;
* the outward tangent-normal direction supports the numerical range; and
* the polynomial boundary values are uniformly bounded by `M`.

The proof derives all remaining facts from the landed infrastructure.  The
resolvent and polynomial kernels are interval integrable, the supporting
half-plane condition makes the double-layer kernel positive, and the
resolvent Cauchy identity gives total mass `4 * pi • 1`.  Positive-kernel
contractivity then gives the factor `2`.

The hypotheses are intentionally explicit: `SmoothJordanDomain` does not
currently record an orientation/support condition, and no general-domain
Cauchy or Plemelj theorem is hidden here.

## Main declaration

* `SmoothJordanDomain.isCompact_frontier` -- the parametrized frontier is
  compact;
* `norm_eval_boundaryParam_le_polynomialSupNorm_frontier` -- boundary values
  are controlled by the polynomial sup norm on the frontier;
* `exists_global_polynomial_calculus_bound_frontier_of_cauchy` -- an
  all-polynomial Cauchy representation supplies a finite global calculus
  constant on the fixed smooth domain;
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support`
  -- the generic smooth-domain L4.2d bound from Cauchy and support data.
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support`
  -- the same estimate with the canonical frontier sup norm.
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support`
  -- control by any compact set containing the frontier.
* `isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support`
  -- the Hermitian product remainder is an integrated positive variance.
* `re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support`
  -- the corresponding accretive quadratic-form statement.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ApproximationSupNorm
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.DoubleLayer
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.DoubleLayerIntegral
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.PositiveIntegral
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ProductContour
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SymmetrizedAuxiliary
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SymmetrizedBound
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace SmoothJordanDomain
end SmoothJordanDomain
private theorem intervalIntegrable_boundaryDatum_smul_outwardKernel
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    IntervalIntegrable
      (fun t => h (Omega.boundaryParam t) •
        ((-I * deriv Omega.boundaryParam t) •
          resolvent A (Omega.boundaryParam t)))
      volume 0 (2 * Real.pi) := by
  have hcontour :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega h hOmega hh
  change IntervalIntegrable
    (fun t => deriv Omega.boundaryParam t •
      (h (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)))
    volume 0 (2 * Real.pi) at hcontour
  have hfun :
      (fun t => h (Omega.boundaryParam t) •
        ((-I * deriv Omega.boundaryParam t) •
          resolvent A (Omega.boundaryParam t))) =
      fun t => (-I) •
        (deriv Omega.boundaryParam t •
          (h (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t))) := by
    funext t
    simp only [smul_smul]
    congr 1
    ring
  rw [hfun]
  exact ⟨hcontour.1.smul_enorm (-I), hcontour.2.smul_enorm (-I)⟩
