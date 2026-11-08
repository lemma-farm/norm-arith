/-
# Crouzeix--Palencia assembly along compact exhaustions

This file joins compact-set sup-norm convergence to the sequence-limit
auxiliary assembly.  It reduces the exact Crouzeix--Palencia conclusion to
constructing the sharp auxiliary bounds at every stage of a decreasing
compact exhaustion of the closed numerical range.

## Main declaration

* `crouzeix_palencia_of_antitone_compact_auxiliary_bounds` -- exact L4.2
  from stagewise auxiliary bounds along a decreasing compact exhaustion.
* `crouzeix_palencia_of_compactThickening_auxiliary_bounds` -- the canonical
  specialization to closed thickenings of the closed numerical range.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ApproximationSupNorm
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.CompactThickeningApprox
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.PalenciaApproximation
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
