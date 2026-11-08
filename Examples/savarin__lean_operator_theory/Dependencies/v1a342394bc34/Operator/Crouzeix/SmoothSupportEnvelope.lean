/-
# Convex envelopes of planar support functions

A real support function determines a closed convex set by intersecting its
directional halfspaces; its interior is the corresponding open convex
carrier.  This file develops the elementary global envelope facts needed by
the smooth support-curve construction.  For rounded finite-polytope supports,
the original convex hull lies in that interior with the explicit rounding
margin.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.PolytopeSoftSupportCurvature
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
