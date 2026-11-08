/-
# Nonemptiness of the numerical range

The numerical range is nonempty exactly when the underlying inner-product
space is nontrivial.  Thus the only empty numerical ranges are those on a
subsingleton space.
-/
import Mathlib
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Basic
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
