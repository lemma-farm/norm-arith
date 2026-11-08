/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Realizing formal-product choices by position sets

This module constructs a basic-factor choice from its mixed and left position
sets and proves the resulting position-count formulas.
-/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation
end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
