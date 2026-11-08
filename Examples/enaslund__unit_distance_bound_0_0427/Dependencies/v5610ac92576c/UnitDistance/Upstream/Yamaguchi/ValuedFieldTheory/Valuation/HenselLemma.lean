/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace ValuationTheory
/-!
# Factorization-shaped Hensel consequences

Mathlib exposes the simple-root form of Hensel's lemma.  The statements below
turn it into a linear-factor lifting API for a simple residual linear factor.
-/
noncomputable section
universe u v
namespace DiscreteValuationField
namespace HenselianDVF
open ValuationTheory.DiscreteValuationField.ResidueField
variable {K : Type u} [Field K]
variable (F : HenselianDVF.{u, v} K)
end HenselianDVF
end DiscreteValuationField
end
end ValuationTheory
