/-
# Induction through boundary-phase divided differences

At a frontier point `xi`, the sharp scalar-companion boundary estimate for a
polynomial `p` contains the phase transform of
`p /ₘ (X - C xi)`.  This quotient has strictly smaller degree whenever `p`
has positive degree, but it depends on `xi`.  Consequently the appropriate
recursive invariant branches over every frontier point rather than following
one fixed remainder polynomial.

This file packages that branching strong induction.  The degree-zero base is
already sharp because the divided difference vanishes.  The resulting L4.2
connector leaves only a cancellation-preserving divided-difference-to-parent
phase step as its phase hypothesis.

## Main declarations

* `CrouzeixBoundaryPhaseContractive` -- the exact sharp frontier invariant;
* `polynomial_induction_on_boundaryPhaseDividedDifferences` -- branching
  strong induction through all frontier-dependent quotients;
* `crouzeixBoundaryPhaseContractive_of_dividedDifference_induction` -- the
  invariant with its degree-zero base discharged;
* `crouzeixBoundaryPhaseContractive_of_normalized` -- reduction to
  positive-degree polynomials of unit frontier sup norm;
* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction`
  -- the L4.2 assembly from the remaining positive-degree phase step.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionAssembly
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
