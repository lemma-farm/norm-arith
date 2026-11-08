/-
# Crouzeix--Palencia assembly on smooth thickening domains

This file connects the concrete closed-thickening exhaustion to the sharp
smooth-boundary symmetrized estimate.  It shows that the full
Crouzeix--Palencia conclusion follows if the open metric thickenings of the
closed numerical range admit compatible smooth Jordan parametrizations with
the polynomial Cauchy and support identities, and if the remaining product
estimate holds at every stage.  It also packages the published companion
route: a uniformly sup-norm-contractive sequence of polynomials converging at
the operator to the canonical auxiliary operator suffices.  The resolvent
Cauchy mass identity is the constant-polynomial specialization of the
polynomial formula.

The hypotheses deliberately expose the remaining analytic gaps.  No
smoothness of an arbitrary metric-thickening frontier, general-domain Cauchy
theorem, polynomial companion approximation, or product inequality is inferred
from the set-theoretic approximation alone.

## Main declaration

* `crouzeix_palencia_of_convexThickening_cauchy_support_product` -- exact
  Crouzeix--Palencia from compatible smooth thickening data and stagewise
  positive-degree product bounds.
* `crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions`
  -- exact Crouzeix--Palencia from the same smooth data and convergent
  polynomial companions.
* `crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions`
  -- the natural additive-error polynomial-approximation interface.
* `crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation`
  -- the published-route interface in terms of contractive interior scalar
  companions, uniform polynomial approximation, and calculus identification.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.CompactThickeningApprox
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.GeneralSymmetrized
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PalenciaExhaustion
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PolynomialCauchyMass
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PolynomialCompanionConvergence
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PolynomialCompanionNormalization
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ProductBase
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Convex
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
