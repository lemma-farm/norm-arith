/-
# Smooth planar curves from support functions

For a smooth periodic real support function `h`, let `n(theta)` be the unit
normal and `tau(theta) = n(theta) * I` the positively oriented unit tangent.
The classical support curve is

`gamma(theta) = h(theta) n(theta) + h'(theta) tau(theta)`.

Its derivative is exactly `(h + h'') tau`.  Thus strict positivity of the
curvature radius `h + h''` gives a smooth periodic regular curve, with explicit
speed and outward-normal formulas.  These local identities are independent of
the later global argument identifying the curve with the frontier of its
support envelope.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PolytopeSoftSupportCurvature
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set
open scoped ContDiff
