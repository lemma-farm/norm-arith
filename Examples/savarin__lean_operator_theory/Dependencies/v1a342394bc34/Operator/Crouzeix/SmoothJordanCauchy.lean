/-
# Cauchy's theorem on smooth convex Jordan domains

A function differentiable in a smooth convex Jordan carrier and continuous
on its closure has zero boundary contour integral.  A Poincaré primitive is
available only in the open carrier, so the proof first integrates along
strict inward homothetic copies of the boundary.  Compact-uniform convergence
of their integrands then transports the zero value to the original contour.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ContourIntegral
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothJordanSupport
import Mathlib
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
