/-
# Convexity of the numerical range

This file proves the Toeplitz--Hausdorff theorem: the numerical range of a
bounded linear operator on a complex inner product space is convex over `ℝ`.
-/
import Mathlib
import Mathlib.Topology.Order.IntermediateValue
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Basic
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Helpers
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
