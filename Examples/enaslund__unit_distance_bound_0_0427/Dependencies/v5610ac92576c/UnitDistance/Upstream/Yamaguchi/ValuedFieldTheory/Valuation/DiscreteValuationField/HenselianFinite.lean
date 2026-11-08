/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower
public import Mathlib
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Nakayama
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace ValuationTheory
/-!
# Finite algebra consequences of Henselian pairs

This file keeps the Nakayama and finite-module completion consequences away
from the lightweight `HenselianDVF` core.
-/
noncomputable section
universe u v
namespace DiscreteValuationField
namespace HenselianDVF
variable {K : Type u} [Field K]
end HenselianDVF
end DiscreteValuationField
end
end ValuationTheory
