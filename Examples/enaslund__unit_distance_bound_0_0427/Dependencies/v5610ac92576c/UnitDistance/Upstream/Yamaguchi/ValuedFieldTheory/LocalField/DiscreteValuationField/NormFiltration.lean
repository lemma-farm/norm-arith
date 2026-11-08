/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace LocalFieldTheory
/-!
# Norm compatibility with unit filtrations

A compatibility hypothesis for a norm and two unit filtrations immediately
produces homomorphisms on every filtration level.
-/
noncomputable section
universe u v
namespace DiscreteValuationField
namespace ValuedNorm
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)
variable (UG : AntitoneSubgroupFiltration G) (UH : AntitoneSubgroupFiltration H)
variable (targetLevel : ℕ → ℕ)
def filtrationPreimageSubgroup (n : ℕ) : Subgroup H :=
  (UG.principalUnitSubgroup (targetLevel n)).comap N.toHom
instance filtrationPreimageSubgroup_normal
    (n : ℕ) [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageSubgroup UG targetLevel n).Normal := by
  dsimp [filtrationPreimageSubgroup]
  infer_instance
/-- The class of the norm-preimage of the target filtration subgroup inside
the source quotient `H ⧸ U_H^n`. -/
def filtrationPreimageClassInQuotient (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal] :
    Subgroup (H ⧸ UH.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UH.principalUnitSubgroup n))
    (N.filtrationPreimageSubgroup UG targetLevel n)
/--
The subgroup appearing in `(N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal` is
normal.
-/
instance filtrationPreimageClassInQuotient_normal
    (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal := by
  dsimp [filtrationPreimageClassInQuotient]
  infer_instance
end ValuedNorm
end DiscreteValuationField
end
end LocalFieldTheory
