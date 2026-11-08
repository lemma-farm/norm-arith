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
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Mathlib
public import Mathlib.Topology.Algebra.Valued.ValuedField
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
universe u v
namespace ValuationTheory
/-!
# Adic completeness of complete rank-one discrete valued fields

This file supplies the common source used in the valuation-topology and adic-completeness arguments: on a
rank-one discrete valued field with archimedean ambient value group, the
native topology of the valuation ring is its maximal-ideal adic topology.
Consequently a complete valued field has an adically complete valuation ring.
-/
noncomputable section
namespace Valuations
open DiscreteValuationField
end Valuations
end
end ValuationTheory
