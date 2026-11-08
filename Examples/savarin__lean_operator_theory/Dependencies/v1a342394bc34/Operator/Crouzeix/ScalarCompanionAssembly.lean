/-
# Assembly from the scalar Plemelj companion

The published fourth-power route to the Crouzeix--Palencia estimate consumes
a continuous scalar companion which is contractive on each compact stage,
uniformly approximable there by polynomials, and whose auxiliary contour is
the conjugate-polynomial auxiliary operator.  This file supplies the bridge
from the canonical Plemelj construction to that interface.

The remaining analytic inputs stay explicit: convergence of the regularized
transform, the sharp lower-degree boundary-phase inequality, uniform
polynomial approximation of the resulting closed extension, and reproduction
of the original auxiliary contour.

## Main declarations

* `exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform`
  packages the canonical closed extension for one smooth domain;
* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation`
  feeds those packages through the smooth-thickening fourth-power capstone.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.BoundaryApproximation
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.PalenciaSmoothApproximation
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionPlemeljBound
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
