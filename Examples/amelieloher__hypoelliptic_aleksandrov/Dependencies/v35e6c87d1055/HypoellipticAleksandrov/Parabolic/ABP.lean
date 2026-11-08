module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.AreaFormula
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.ContactCoverage
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth determinant-weighted parabolic ABP estimate

This module combines first-contact coverage, the one-sided area formula, and
the pointwise Jacobian bound into the exact power-form smooth parabolic
Aleksandrov--Bakelman--Pucci estimate on a unit velocity ball.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder
end HypoellipticAleksandrov.Parabolic
