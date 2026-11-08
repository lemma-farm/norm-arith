/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Valued.NormedValued
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Topology of range-restricted complete discretely valued fields

This file equips the multiplicative-range valuation with its valued and normed
field structures and transports adic completeness, compactness, properness,
and completeness.
-/
noncomputable section
universe u v
open Filter WithZero
open scoped NNReal Valued Filter WithZero
namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
variable {K : Type u} [Field K]
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
