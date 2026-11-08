/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace ValuationTheory
/-!
# Valuation-extension API for Henselian discretely valued fields

This file keeps the valuation-extension uniqueness interface separate from the
lightweight Henselian-DVF core.  The core file is used by Hensel lifting and
does not need to import mathlib's full `Valuation.HasExtension` API.
-/
noncomputable section
universe u v w x y
namespace DiscreteValuationField
namespace HenselianDVF
variable {K : Type u} [Field K]
variable {L : Type w} [Field L] [Algebra K L]
end HenselianDVF
end DiscreteValuationField
end
end ValuationTheory
