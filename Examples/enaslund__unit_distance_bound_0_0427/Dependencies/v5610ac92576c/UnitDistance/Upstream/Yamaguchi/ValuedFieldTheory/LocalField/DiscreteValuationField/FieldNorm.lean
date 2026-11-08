/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Mathlib
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NormUnits
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace LocalFieldTheory
/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/
noncomputable section
universe u v w
namespace DiscreteValuationField
variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]
def fieldNormFiltrationPreimageSubgroup
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ) :
    Subgroup Lˣ :=
  (UK.principalUnitSubgroup (targetLevel n)).comap (normUnits K L)
instance fieldNormFiltrationPreimageSubgroup_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageSubgroup]
  infer_instance
/-- The class of the field-norm preimage of the target filtration subgroup
inside the source filtration quotient. -/
def fieldNormFiltrationPreimageClassInQuotient
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal] :
    Subgroup (Lˣ ⧸ UL.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UL.principalUnitSubgroup n))
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n)
/--
The subgroup appearing in `(fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel
n).Normal` is normal.
-/
instance fieldNormFiltrationPreimageClassInQuotient_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageClassInQuotient
      K L UK UL targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageClassInQuotient]
  infer_instance
end DiscreteValuationField
end
end LocalFieldTheory
