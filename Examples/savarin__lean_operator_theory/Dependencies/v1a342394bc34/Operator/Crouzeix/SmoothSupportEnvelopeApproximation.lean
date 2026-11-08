/-
# Quantitative approximation by smooth support envelopes

For a nonempty finite point set, the rounded log-sum-exp support envelope is
not only an outer neighborhood of its convex hull: it lies in the closed
metric thickening whose radius is the uniform log-sum-exp overshoot.  The
proof uses the nearest-point characterization for closed convex sets and the
direction of the displacement from a nearest point.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothSupportEnvelope
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
