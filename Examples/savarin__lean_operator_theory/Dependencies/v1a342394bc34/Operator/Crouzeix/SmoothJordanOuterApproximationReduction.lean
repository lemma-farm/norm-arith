/-
# Reducing smooth outer approximation to the full-dimensional case

For a nonempty compact convex planar set, it is enough to construct smooth
Jordan outer approximations when the set has nonempty interior.  Before
invoking that case, replace the target by its closed half-scale thickening.
This thickening is still compact and convex, has nonempty interior, and a
second half-scale thickening fits inside the requested original scale.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothJordanOuterApproximation
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
