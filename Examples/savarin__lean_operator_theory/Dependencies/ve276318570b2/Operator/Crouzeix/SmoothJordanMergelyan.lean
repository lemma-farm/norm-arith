/-
# Polynomial approximation from smooth-Jordan Cauchy formulas

This file converts a normalized scalar Cauchy formula on a compact smooth
convex Jordan carrier into uniform polynomial approximation on its closure.
Strict radial contraction moves the evaluation point into the carrier and
turns each boundary kernel into one whose pole lies strictly outside the
closed carrier.  `ConvexRungeIntegral` approximates each radialized function,
and a diagonal selection removes the radial contraction.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ConvexRungeIntegral
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.SmoothJordanCauchyFormula
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.SmoothJordanExhaustion
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology
private noncomputable def smoothMergelyanRadialFactor (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / ((n : ℝ) + 2)
private theorem one_sub_smoothMergelyanRadialFactor (n : ℕ) :
    1 - smoothMergelyanRadialFactor n = 1 / ((n : ℝ) + 2) := by
  unfold smoothMergelyanRadialFactor
  have hn : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hn]
  ring
