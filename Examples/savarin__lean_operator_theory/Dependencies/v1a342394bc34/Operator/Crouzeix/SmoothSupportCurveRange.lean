/-
# Exact frontier range of rounded support curves

This file proves the reverse inclusion missing from the global support-curve
calculus: every frontier point of a bounded rounded support envelope is hit by
the support curve.  The key local fact is that an active support inequality
recovers both normal and tangent coordinates of the contact point.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportCurveGlobal
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped ContDiff
