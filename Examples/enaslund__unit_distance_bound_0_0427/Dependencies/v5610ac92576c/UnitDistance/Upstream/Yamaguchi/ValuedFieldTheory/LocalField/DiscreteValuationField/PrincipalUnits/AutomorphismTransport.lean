/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace LocalFieldTheory
open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField
/-!
# Automorphism transport for principal units

A field automorphism preserving the chosen valuation ring acts on the valuation ring,
its residue field, its units, and every principal-unit quotient.
-/
noncomputable section
open scoped BigOperators
universe u v
namespace DiscreteValuationField
namespace CompleteDVF
variable {K : Type u} [Field K]
namespace higherPrincipalUnitGroup
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
end higherPrincipalUnitGroup
end CompleteDVF
end DiscreteValuationField
end
end LocalFieldTheory
