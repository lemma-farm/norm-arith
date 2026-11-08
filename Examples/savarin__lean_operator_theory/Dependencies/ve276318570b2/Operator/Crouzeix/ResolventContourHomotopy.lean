/-
# Affine homotopy invariance of the resolvent contour mass

The contour integral of the operator resolvent is constant along a commuting
affine operator path as long as the contour stays in the resolvent set.  For
the path from a scalar operator `c • 1` to `A`, convexity of the carrier and
the spectral inclusion `spectrum A ⊆ closure (numericalRange A)` provide that
resolvent-set condition.  Oriented scalar winding then computes the common
mass as `2 * pi * I • 1`.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ScalarCauchyKernelWinding
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.SpectralSet.SpectrumInNR
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
