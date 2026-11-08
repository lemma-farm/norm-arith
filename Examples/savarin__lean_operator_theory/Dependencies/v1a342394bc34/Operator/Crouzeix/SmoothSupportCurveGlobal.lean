/-
# Global geometry of smooth support curves

For a smooth periodic support function with positive curvature radius, every
fixed directional projection of its support curve increases strictly until
the matching normal angle and decreases strictly afterward.  Periodicity then
turns this local derivative calculation into global support-halfspace control,
uniqueness of the supporting contact, and injectivity on every fundamental
period.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportCurve
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportEnvelopeApproximation
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped ContDiff
