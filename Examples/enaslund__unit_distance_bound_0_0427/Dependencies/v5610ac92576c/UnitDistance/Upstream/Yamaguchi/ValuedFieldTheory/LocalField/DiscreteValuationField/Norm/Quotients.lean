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
public import Mathlib
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic
@[expose] public section
set_option backward.privateInPublic true
/-!
Develops quotient groups attached to an abstract valued norm, including kernel, image, and
representative criteria.
-/
/-!
Identifies norm-quotient classes with valuation classes modulo the residue degree and constructs
the resulting cyclic equivalences.
-/
set_option autoImplicit false
namespace LocalFieldTheory
noncomputable section
universe u v
namespace DiscreteValuationField
namespace ValuedNorm
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)
def normSubgroup : Subgroup G :=
  N.toHom.range
def valueModResidueDegreeHom :
    G →* Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.mk'
      (integerMultipleSubgroup (N.residueDegree : ℤ))).comp
    vG.valuationHom
def residueDegreeClassSubgroup :
    Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup)
    N.valueModResidueDegreeHom.ker
/-- The subgroup appearing in `N.residueDegreeClassSubgroup.Normal` is normal. -/
instance residueDegreeClassSubgroup_normal :
    N.residueDegreeClassSubgroup.Normal := by
  dsimp [residueDegreeClassSubgroup]
  infer_instance
def normSubgroupClassInZeroQuotient : Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup) N.normSubgroup
/-- The subgroup appearing in `N.normSubgroupClassInZeroQuotient.Normal` is normal. -/
instance normSubgroupClassInZeroQuotient_normal
    [(N.normSubgroup).Normal] :
    N.normSubgroupClassInZeroQuotient.Normal := by
  dsimp [normSubgroupClassInZeroQuotient]
  infer_instance
end ValuedNorm
end DiscreteValuationField
end
end LocalFieldTheory
universe u v
namespace LocalFieldTheory
noncomputable section
namespace DiscreteValuationField
namespace ValuedNorm
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)
end ValuedNorm
end DiscreteValuationField
end
end LocalFieldTheory
