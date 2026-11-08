/-
# Boundary approximation implies polynomial-companion convergence

For any continuous scalar boundary datum, if polynomials approximate that
datum uniformly and satisfy the polynomial Cauchy representation, their
evaluations at the operator converge in norm to the associated normalized
resolvent contour integral.  The canonical Crouzeix auxiliary operator is the
specialization to the conjugate boundary values of a polynomial.

This file makes the passage quantitative.  Compactness of the parameter
interval bounds `deriv γ(t) • resolvent A (γ(t))` by a fixed constant, so a
boundary error of `1 / (j + 1)` gives an operator error bounded by a fixed
multiple of the same null sequence.

## Main declaration

* `tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation`
  -- the generic continuous-boundary-datum convergence theorem.
* `tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation`
  -- its conjugate-polynomial specialization.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.AuxOperator
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
