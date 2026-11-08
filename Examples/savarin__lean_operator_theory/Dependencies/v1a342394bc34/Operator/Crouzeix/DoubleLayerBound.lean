/-
# The normalized positive-kernel bound for the double layer

The double-layer kernel in the Crouzeix--Palencia argument has total mass
`4 * pi • 1`, while the contour representation of the symmetrized operator
has the real normalization factor `(2 * pi)⁻¹`.  Contractivity of integration
against a positive operator kernel therefore gives the sharp factor `2`.

This file records precisely that scaling step.  The positivity,
integrability, and mass identity remain explicit inputs, so the theorem can
be applied after the geometric and Cauchy-integral parts of the argument have
identified the concrete double-layer kernel.

## Main declaration

* `norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg` -- a positive
  kernel of mass `4 * pi • 1`, normalized by `(2 * pi)⁻¹`, integrates every
  scalar weight bounded by `M` to an operator of norm at most `2 * M`.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.DoubleLayerIntegral
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.PositiveKernelBound
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
