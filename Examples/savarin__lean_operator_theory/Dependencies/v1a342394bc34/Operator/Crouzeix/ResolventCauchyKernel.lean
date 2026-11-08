/-
# The exterior resolvent Cauchy kernel

The scalar Cauchy kernel vanishes outside a closed convex carrier.  Combining
that fact with the two-parameter resolvent identity evaluates the nested
operator kernel

`(2 * pi * I)⁻¹ ∮ (sigma - z)⁻¹ R_A(z) dz = R_A(sigma)`.

This is the inner-contour calculation needed to identify the scalar companion
functional calculus with the original conjugate-polynomial auxiliary contour.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCauchyKernelConstancy
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.CircleCauchy
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
