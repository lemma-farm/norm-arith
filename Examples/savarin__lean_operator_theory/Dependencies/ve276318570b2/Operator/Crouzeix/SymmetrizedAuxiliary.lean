/-
# Symmetrized polynomial auxiliary operator

The L4.2d estimate identifies `p(A) + G†` with a polynomial-weighted
double-layer integral.  This file proves that identification from the
explicit Cauchy representation of `p(A)`.  The remaining analytic input is
kept as a named hypothesis, so a circle or general contour Cauchy theorem can
supply it without changing the algebraic interface.

## Main declaration

* `aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy`
  -- the normalized symmetrized auxiliary operator is the polynomial-weighted
  integral of the resolvent double-layer kernel.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.AdjointIntegral
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.AuxOperator
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
