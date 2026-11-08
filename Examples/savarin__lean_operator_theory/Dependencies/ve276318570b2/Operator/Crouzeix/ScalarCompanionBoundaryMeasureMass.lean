/-
# Automatic mass of the boundary double-layer density

For an oriented smooth convex Jordan boundary, the double-layer density

`rho_xi(t) = Im (gamma'(t) / (gamma(t) - xi)) / pi`

has mass one at every frontier point.  The proof chooses a parameter `s` for
`xi`, divides the boundary chord by `gamma'(s)`, and rotates it by `-I`.
Convex support puts this normalized chord in `Complex.slitPlane`.  Its
principal argument therefore lifts continuously from `0` to `pi` during one
period, and its derivative is exactly `pi * rho_xi`.  Positivity makes the
lift monotone, which supplies derivative integrability; the improper
fundamental theorem then gives the mass identity.

## Main declarations

* `crouzeixBoundaryDoubleLayerDensity_periodic` -- the density is periodic;
* `canonicalNormal_support_all_of_Ioc` -- oriented support on one fundamental
  interval propagates to every parameter;
* `integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point`
  -- one consistently oriented carrier point forces unit mass at every
  frontier basepoint;
* `crouzeixBoundaryPhaseContractive_of_oriented_carrier_point` -- the same
  geometry gives sharp boundary-phase contractivity for every polynomial.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ScalarCompanionBoundaryMeasure
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.SmoothJordanSupport
import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
