/-
# Constant-polynomial base case for the auxiliary product bound

The recursive product decomposition in `ProductContour.lean` lowers the
degree of its polynomial remainder.  This file supplies the corresponding
degree-zero base case on an arbitrary smooth contour satisfying the raw
resolvent Cauchy identity.

For `p = C a`, the conjugate-polynomial auxiliary operator is
`star a • 1`.  Hence `p(A) G` has norm `‖a‖²`, which is exactly the square of
the polynomial sup norm on every nonempty set.

## Main declarations

* `polynomialSupNorm_C_of_nonempty` -- the sup norm of a constant polynomial.
* `normalized_contourIntegral_resolvent_eq_one_of_cauchy` -- normalization of
  the raw resolvent Cauchy mass identity.
* `crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one` -- the auxiliary
  operator for a constant polynomial.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero`
  -- the sharp L4.2e base case.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ProductContour
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.VonNeumann
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
