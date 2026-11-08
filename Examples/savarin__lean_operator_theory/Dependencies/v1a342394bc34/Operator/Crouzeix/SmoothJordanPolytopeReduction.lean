/-
# Reducing smooth outer approximation to convex polytopes

Every compact convex subset of a finite-dimensional real normed space can be
sandwiched between itself and any prescribed neighborhood by the convex hull
of finitely many points, with the original set contained in the interior of
that hull.  Applying this theorem in the complex plane reduces the remaining
smooth outer-approximation problem to full-dimensional convex polytopes.

The two half-scale thickenings in the proof compose to the originally
requested scale.  Consequently the same finite-convex-hull hypothesis reaches
the exact Crouzeix--Palencia operator bound.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothJordanOuterApproximationReduction
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
