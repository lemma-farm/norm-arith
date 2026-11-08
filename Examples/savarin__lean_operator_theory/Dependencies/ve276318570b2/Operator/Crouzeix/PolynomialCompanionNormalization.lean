/-
# Normalize approximate polynomial companions

Uniform polynomial approximation naturally gives a scalar sup-norm bound with
an arbitrarily small additive error.  The fourth-power Crouzeix--Palencia
bootstrap instead consumes an exactly contractive sequence.  This file bridges
those interfaces by shrinking the `j`-th approximant by
`m / (m + 1 / (j + 1))`.  The shrinkage factors tend to one, so the operator
limit is unchanged.

The zero case necessarily needs separate information: exact contractivity at
`m = 0` forces every normalized polynomial to vanish, and hence can converge
only to zero.  This condition is explicit in the generic statement; for the
canonical Crouzeix auxiliary operator it follows from vanishing of the source
polynomial on an infinite compact control set.

## Main declaration

* `exists_tendsto_polynomial_companions_of_add_one_div_bounds` -- convert
  additive `1 / (j + 1)` sup-norm errors into an exactly contractive sequence
  without changing the operator-norm limit.
* `polynomialSupNorm_le_add_of_uniform_approximation` -- a contractive scalar
  target and a uniform polynomial approximation give the required additive
  sup-norm bound.
* `exists_tendsto_polynomial_companions_of_uniform_approximation` -- combine
  uniform approximation of a contractive scalar companion with exact
  normalization.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PolynomialSupNormZero
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
