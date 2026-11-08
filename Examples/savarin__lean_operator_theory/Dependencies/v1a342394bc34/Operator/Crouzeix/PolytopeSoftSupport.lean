/-
# Smooth support functions for finite planar polytopes

The directional support function of a finite convex hull is a maximum of
finitely many sinusoidal functions and is generally not smooth.  Its
log-sum-exp regularization is infinitely differentiable and periodic.  This
file records the exact one-sided bounds: it dominates every vertex support
value and exceeds any common upper bound by at most `delta * log(card)`.

These estimates are the quantitative input for constructing a smooth convex
support curve around a polygon.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothJordanPolytopeReduction
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set
open scoped ContDiff
