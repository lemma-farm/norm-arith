/-
# Quantitative bounds for the regularized Plemelj value

Polynomial division by `X - C xi` factors the cancelled boundary numerator.
Consequently, the apparent singular phase in the regularized self-value has
unit norm, and a bound on the speed of the boundary parametrization gives an
explicit estimate in terms of the frontier sup norm of the divided-difference
polynomial.

This is not the final sharp companion contraction: it isolates the additional
divided-difference term that a sharp boundary argument must control.

## Main declarations

* `norm_crouzeixPolynomialScalarCompanionRegularized_self_le` -- the explicit
  bound for a chosen boundary-speed constant.
* `crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic` -- the
  exact lower-degree phase-weighted contour representation.
* `crouzeixPolynomialBoundaryPhaseTransform` -- the named lower-degree phase
  contour carrying the remaining sharp frontier estimate.
* `crouzeixPolynomialBoundaryPhaseTransform_add` and `_smul` -- its
  conjugate-linear polynomial API.
* `norm_crouzeixPolynomialBoundaryPhaseTransform_le` -- its explicit
  domain-speed norm bound.
* `exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le`
  -- one domain-only constant works for all polynomials and base points.
* `norm_crouzeixPolynomialScalarCompanionBoundaryValue_le` -- the resulting
  quantitative bound for the explicit Plemelj boundary value.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ProductBase
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionDecay
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionPlemelj
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set
open scoped Interval Real
