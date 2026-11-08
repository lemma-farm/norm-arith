/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Restricting a valuation to its multiplicative range

The restricted valuation has the same valuation ring, maximal ideal, and
residue field as the original valuation.
-/
noncomputable section
universe u x
open WithZero
open scoped NNReal Valued WithZero
namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace WithZeroValuation
variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]
section Field
variable [Field R]
variable {K : Type u} [Field K]
end Field
end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField
end
