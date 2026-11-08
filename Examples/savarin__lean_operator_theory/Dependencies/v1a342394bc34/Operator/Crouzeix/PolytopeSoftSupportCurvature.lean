/-
# Curvature of finite soft support functions

For the log-sum-exp regularization `h` of a finite directional support
function, the support-curve curvature radius is `h + h''`.  This file computes
the two derivatives through the finite exponential partition and proves that
this radius is nonnegative.  The proof separates into two elementary finite
inequalities: each exponent is bounded by the log partition, and weighted
Cauchy--Schwarz makes the velocity variance nonnegative.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.PolytopeSoftSupport
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set
open scoped ContDiff
