/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Valuation estimates for logarithm and exponential series

This file proves lower bounds and divergence-to-infinity statements for the
integer valuations of the logarithm and exponential series terms.
-/
noncomputable section
universe u
open Filter WithZero
open scoped NNReal Filter WithZero
namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation
variable {K : Type u} [Field K]
end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
