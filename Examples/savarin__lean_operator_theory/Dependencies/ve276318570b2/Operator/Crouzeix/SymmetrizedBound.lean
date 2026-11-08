/-
# Assembly of the symmetrized double-layer bound

This file packages the last norm-estimate step of L4.2d.  Once an operator
sum `F + G†` has been represented as the `(2 * pi)⁻¹`-normalized integral of
a scalar weight against a positive operator kernel of total mass
`4 * pi • 1`, positive-kernel contractivity gives the sharp estimate
`norm (F + G†) ≤ 2 * M`.

All analytic and geometric inputs remain visible in the theorem statement:
the representation, interval integrability, positivity, mass normalization,
and scalar boundary bound.  The theorem therefore composes directly with a
Cauchy representation of `p(A) + G†` without asserting that missing identity
itself.

## Main declaration

* `norm_add_star_le_two_mul_of_doubleLayer_representation` -- the final
  factor-two norm estimate from a normalized positive double-layer
  representation.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.DoubleLayerBound
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
