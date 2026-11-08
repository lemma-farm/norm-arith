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
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import Mathlib
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Data.Int.WithZero
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.RingTheory.Valuation.RankOne
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Cyclic value groups and normalized uniformizers

This file supplies the ordered-group and rank-one facts used for actual
multiplicative valuation ranges, together with normalized uniformizer results
for `ℤᵐ⁰`-valued valuations.
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
open LinearOrderedCommGroup
end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField
end
