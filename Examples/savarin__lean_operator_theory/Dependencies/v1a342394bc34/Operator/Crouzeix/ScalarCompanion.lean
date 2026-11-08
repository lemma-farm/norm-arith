/-
# The scalar Crouzeix--Palencia companion

For a polynomial `p` and a smooth Jordan domain `Omega`, the published
Crouzeix--Palencia proof uses the scalar Cauchy companion

`g(z) = (2πi)⁻¹ ∮∂Ω conj(p(σ)) / (σ - z) dσ`.

This file defines that function using the project's parameterized contour
integral and proves it is holomorphic throughout `Omega.carrier`.  The proof
differentiates under the interval integral.  Around each interior point, an
open ball remains disjoint from the compact parametrized frontier; this gives
the uniform inverse-square bound required by the dominated derivative theorem.

The remaining sharp analytic input is not hidden here: extending the companion
continuously to the boundary and proving its sup-norm contraction require a
Plemelj boundary-value argument.

## Main declarations

* `crouzeixPolynomialScalarCompanion` -- the scalar Cauchy companion.
* `crouzeixPolynomialScalarCompanionDeriv` -- its inverse-square derivative
  integral.
* `crouzeixPolynomialScalarCompanion_smul` -- the companion and its derivative
  are conjugate-homogeneous in the polynomial.
* `crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one` -- the
  companion is the scalarization of the one-dimensional auxiliary operator.
* `norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator` -- this
  scalarization preserves the operator norm exactly.
* `hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier` -- the
  exact derivative formula away from the boundary.
* `analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl` -- the
  interior and exterior holomorphic branches.
* `hasDerivAt_crouzeixPolynomialScalarCompanion` and
  `analyticOn_crouzeixPolynomialScalarCompanion` -- their interior forms.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.AuxOperator
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
