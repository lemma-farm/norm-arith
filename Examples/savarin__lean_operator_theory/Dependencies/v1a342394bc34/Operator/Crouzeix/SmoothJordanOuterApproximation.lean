/-
# From local smooth outer approximation to a nested exhaustion

An exact realization of every metric thickening by a smooth Jordan domain is
far stronger than the planar approximation theorem needed by the
Crouzeix--Palencia assembly.  This file isolates the correct local statement:
for every positive radius there is a smooth Jordan domain between `K` and
that radius's open thickening of `K`.

Compactness then turns these independent approximations into a strict nested
exhaustion.  At each successor stage, a closed thickening of `K` is chosen
inside the preceding open carrier, and the next approximation radius is also
bounded by `1/(n+1)`.  The first bound gives strict nesting; the second makes
the intersection exactly `K`.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothJordanMergelyanAssembly
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
