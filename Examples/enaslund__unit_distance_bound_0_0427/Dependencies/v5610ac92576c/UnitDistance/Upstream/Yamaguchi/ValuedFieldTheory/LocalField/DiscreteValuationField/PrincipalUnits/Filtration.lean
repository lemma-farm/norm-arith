/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
public import Mathlib
public import Mathlib.Algebra.Group.Units.Hom
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace LocalFieldTheory
open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField
/-!
# Principal-unit filtration from a valuation ring

For a complete DVF `F`, the concrete principal-unit filtration on the unit group
of the valuation ring is

`U^n = { u | u - 1 ∈ m^n }`.

This file turns that definition into the abstract `AntitoneSubgroupFiltration`
used by ramification and norm arguments.
-/
noncomputable section
open scoped BigOperators
universe u v
namespace DiscreteValuationField
namespace CompleteDVF
variable {K : Type u} [Field K]
/-- The concrete `n`-th principal-unit subgroup of the valuation ring unit group. -/
def higherPrincipalUnitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) (n : ℕ) :
    Subgroup F.valuationSubringˣ where
  carrier := {u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    have hxy :
        ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 =
          (x : F.valuationSubring) * ((y : F.valuationSubring) - 1) +
            ((x : F.valuationSubring) - 1) := by
      simp
      ring
    change ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxy]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) hx
  inv_mem' := by
    intro x hx
    have hxinv :
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
      calc
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) -
              ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
                (x : F.valuationSubring) := by
          simp
        _ = -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
          ring
    change ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxinv]
    exact (F.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left (F.maximalIdeal ^ n)
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) hx)
namespace higherPrincipalUnitGroup
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
/--
Characterizes `u ∈ higherPrincipalUnitGroup F n` by the equivalent condition `(u :
F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n`.
-/
@[simp] theorem mem_iff (n : ℕ) (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F n ↔
      (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n :=
  Iff.rfl
/-- Higher levels are contained in lower levels. -/
theorem antitone {m n : ℕ} (h : m ≤ n) :
    higherPrincipalUnitGroup F n ≤ higherPrincipalUnitGroup F m := by
  intro u hu
  exact (Ideal.pow_le_pow_right h) hu
end higherPrincipalUnitGroup
end CompleteDVF
end DiscreteValuationField
end
end LocalFieldTheory
