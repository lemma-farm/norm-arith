/-
# Smooth Jordan domains from rounded finite support functions

The rounded log-sum-exp support curve and its open halfspace envelope provide
all fields of `SmoothJordanDomain`.  This file packages that construction and
uses arbitrarily tight scale choices to discharge the remaining planar outer
approximation problem, culminating in the exact polynomial
Crouzeix--Palencia theorem.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportCurveRange
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportEnvelopeTight
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
