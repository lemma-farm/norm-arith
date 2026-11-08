/-
# Resolvent mass from the polynomial Cauchy representation

The normalized operator-valued Cauchy representation for every polynomial
already contains the raw resolvent mass identity: specialize it to the
constant polynomial `1` and clear the nonzero scalar `2πi`.

## Main declaration

* `contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy` --
  derives the raw resolvent contour identity from polynomial Cauchy data.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.AuxOperator
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
