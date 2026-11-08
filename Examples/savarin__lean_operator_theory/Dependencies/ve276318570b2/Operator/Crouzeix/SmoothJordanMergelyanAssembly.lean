/-
# Crouzeix--Palencia assembly from smooth Jordan geometry

The unconditional Mergelyan theorem for smooth convex Jordan domains removes
the analytic approximation hypotheses from the terminal exhaustion
assemblies.  What remains is purely geometric: construct a strictly nested
smooth Jordan exhaustion, or realize the explicit convex thickenings by such
domains.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.SmoothJordanMergelyan
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
