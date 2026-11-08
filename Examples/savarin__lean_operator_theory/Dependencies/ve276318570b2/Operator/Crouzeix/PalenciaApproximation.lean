/-
# Crouzeix--Palencia assembly from approximate auxiliary bounds

Smooth-domain approximation naturally produces auxiliary operators whose
sharp bounds contain an arbitrarily small scalar error.  This file removes
that error after applying the algebraic Crouzeix--Palencia balance estimate.

## Main declarations

* `norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds` -- the
  abstract epsilon-limit form of the balance estimate.
* `crouzeix_palencia_of_approximate_auxiliary_bounds` -- the corresponding
  polynomial spectral-set package over the closure of the numerical range.
* `norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds` and
  `crouzeix_palencia_of_tendsto_auxiliary_bounds` -- sequence-limit forms
  suited to a smooth exhaustion.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.Palencia
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Filter
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
