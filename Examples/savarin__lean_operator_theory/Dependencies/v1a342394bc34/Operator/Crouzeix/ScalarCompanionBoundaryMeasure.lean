/-
# The boundary double-layer probability density

For a boundary point `xi` and a smooth parametrization `gamma`, the scalar
double-layer density is

`rho_xi(t) = Im (gamma'(t) / (gamma(t) - xi)) / pi`.

The Crouzeix--Palencia boundary companion is integration of the conjugate
polynomial datum against this density.  The key cancellation is exact: the
second half of the double-layer kernel is the conjugate of the contour of a
polynomial divided difference, hence integrates to zero on the closed curve.

Consequently, integrability, nonnegativity, and unit mass of this explicit
density imply the sharp boundary-phase contraction.  This file isolates
those two geometric facts rather than assuming the contraction itself.

## Main declarations

* `crouzeixBoundaryDoubleLayerDensity` -- the explicit real density;
* `contourIntegral_polynomial_eval_eq_zero` -- polynomial contours vanish on
  every smooth closed boundary;
* `crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity`
  -- the exact probability-integral representation;
* `crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity` -- sharp
  phase contractivity from nonnegativity and unit mass;
* `crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support`
  -- the sharp invariant from unit mass and oriented support alone.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionPhaseInduction
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionRadial
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
