/-
# Quantitative decay of the scalar companion

The scalar Crouzeix--Palencia companion is a Cauchy transform supported on
the compact Jordan frontier.  This file records the elementary quantitative
part of its exterior normalization: the numerator is uniformly bounded on
the parameter interval, so the transform is bounded by the reciprocal of
the distance to the frontier and therefore tends to zero at infinity.

These facts are useful inputs to a future Plemelj jump argument.  They do not
assert boundary continuity or the sharp companion contraction.

## Main declarations

* `exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator` -- a
  uniform parameter-interval numerator bound.
* `exists_nonneg_bound_boundaryParam_deriv` -- a domain-only bound for the
  boundary speed.
* `norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation` -- the
  explicit inverse-separation estimate.
* `norm_crouzeixPolynomialScalarCompanion_le_infDist` -- its canonical
  distance-to-frontier form.
* `exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist` -- one
  domain constant controls all polynomials by their frontier sup norm.
* `tendsto_crouzeixPolynomialScalarCompanion_cocompact` -- the exterior
  companion tends to zero at infinity.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.GeneralSymmetrized
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanion
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter Set
open scoped Interval Real
