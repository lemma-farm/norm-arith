/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Uniformizers and unit subgroups for induced integer valuations

This file relates the induced integer valuation to normalized uniformizers,
valuation-ring units, and scalar extension of field units.
-/
noncomputable section
universe u
open WithZero
open scoped WithZero
namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation
variable {K : Type u} [Field K]
variable {L : Type u} [Field L] [Algebra K L]
end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
