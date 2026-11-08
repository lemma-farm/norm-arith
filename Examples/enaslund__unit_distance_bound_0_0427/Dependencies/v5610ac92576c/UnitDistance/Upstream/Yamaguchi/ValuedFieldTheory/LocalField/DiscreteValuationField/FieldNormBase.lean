/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Base-unit norm images in field towers

This file isolates the purely algebraic source for the Abhyankar norm-image
argument: embedded base units, their powered image in a lower branch, and the
image obtained after applying the lower norm.  The only theorem used is field
norm transitivity.
-/
noncomputable section
universe u
namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
section BaseUnits
variable {K L : Type u}
variable [Field K] [Field L] [Algebra K L]
end BaseUnits
section Tower
variable {K L M : Type u}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsScalarTower K L M]
end Tower
section LowerNormTower
variable {K L M : Type u}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra L M]
end LowerNormTower
section NormDownTower
variable {K L M : Type u}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra L M]
variable [Algebra K M] [IsScalarTower K L M] [Module.Free L M]
end NormDownTower
end LocalFieldTheory.DiscreteValuationField
end
