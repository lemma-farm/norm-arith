/-
# Arbitrarily tight rounded support envelopes

The quantitative support-envelope estimate becomes an arbitrary open
neighborhood estimate after choosing the smoothing and rounding scales.  We
record an explicit choice that remains valid even for one-point finite sets,
where the logarithmic cardinality term vanishes.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportEnvelopeApproximation
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportCurve
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped ContDiff
