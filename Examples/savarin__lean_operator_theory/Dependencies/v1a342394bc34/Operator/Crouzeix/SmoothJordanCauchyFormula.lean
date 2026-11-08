/-
# Cauchy's integral formula on smooth convex Jordan domains

The smooth-Jordan Cauchy theorem extends to the Cauchy integral formula by
removing the apparent singularity with `dslope`.  The resulting identity is
first stated using the raw scalar contour mass, then normalized under winding
one.  Oriented and canonical-orientation corollaries expose the forms needed
by polynomial approximation on smooth convex domains.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothJordanCauchy
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCauchyKernelWinding
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
