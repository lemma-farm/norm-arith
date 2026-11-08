/-
# L4.2 assembly with automatic scalar Plemelj convergence

Radial regularization on bounded smooth Jordan carriers supplies the full
frontier convergence previously threaded through the scalar-companion
assembly as an analytic hypothesis.  This file removes that hypothesis from
the one-domain companion package and from the smooth-thickening L4.2
capstone.

The remaining inputs are the genuinely sharp phase contraction, polynomial
approximation, and reproduction of the polynomial auxiliary contour.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionAssembly
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionPhaseInduction
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ScalarCompanionRadial
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
