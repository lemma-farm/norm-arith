/-
# Crouzeix--Palencia assembly from auxiliary-operator bounds

This file isolates two algebraic routes to the Crouzeix--Palencia constant.
The project-specific sharp-product route assumes that, for `F = p(A)`, an
auxiliary operator `G` satisfies

* `‖F + G⋆‖ ≤ 2m`, and
* `‖F G‖ ≤ m²`,

then the C⋆-identity gives the quadratic inequality
`‖F‖² ≤ 2m‖F‖ + m²`, hence `‖F‖ ≤ (1 + √2)m`.

This sharp product bound is not the invariant used in the published 2017
proof.  The Crouzeix--Palencia argument, in the shorter
Ransford--Schwenninger formulation, instead combines a contractive scalar
Cauchy-transform companion with an a priori finite norm `K` for the whole
functional calculus.  Its fourth-power bootstrap gives
`K⁴ ≤ 2K³ + K²`, hence the same constant.  Both algebraic endpoints are
formalized below; their distinct analytic hypotheses remain explicit.

## Main declarations

* `norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds` -- the C⋆-algebraic
  quadratic estimate.
* `norm_fourth_power_le_of_companion_calculus_bounds` -- the published
  Ransford--Schwenninger fourth-power bridge from a contractive companion and
  a global functional-calculus bound.
* `norm_fourth_power_le_of_polynomial_companion_calculus_bounds` -- the exact
  polynomial-companion specialization, including the multiplicative triple
  estimate from compact-set sup norms.
* `norm_fourth_power_le_of_tendsto_polynomial_companions` -- passage from
  uniformly contractive polynomial companions to their operator-norm limit.
* `le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq` -- the scalar fixed
  point which closes that bridge.
* `crouzeix_palencia_of_global_polynomial_bound_of_fourth_power` -- its exact
  polynomial spectral-set capstone.
* `four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub` -- the exact symmetric
  minus antisymmetric quadratic-form identity for the auxiliary product.
* `two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq` --
  the corresponding exact Hermitian decomposition of a separated remainder.
* `re_inner_mul_lower_iff_norm_adjoint_sub_sq_le` -- its sharp lower-bound
  reformulation as a relative skew contraction.
* `crouzeix_palencia_of_auxiliary_bounds` -- packages the estimate and the
  landed spectrum inclusion as a polynomial spectral-set result.
* `crouzeix_palencia_of_polynomial_auxiliary_bounds` -- specializes that
  package to the contour operator constructed in `AuxOperator.lean`.
* `crouzeix_palencia_of_isStarNormal` -- the sharper normal-operator branch.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.AuxOperator
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.SpectralSet.Normal
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
