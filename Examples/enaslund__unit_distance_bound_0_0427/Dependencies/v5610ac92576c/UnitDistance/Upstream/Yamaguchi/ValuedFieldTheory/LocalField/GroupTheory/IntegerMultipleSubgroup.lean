/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Mathlib
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic
@[expose] public section
set_option backward.privateInPublic true
/-!
# Integer multiple subgroups

Pure group-theoretic infrastructure for the subgroup of multiplicative
integers divisible by a fixed integer and its cyclic quotient. It lives below
the discrete-valuation-field layer so generic power-index code does not depend
on valued-field norm modules.

The declarations retain the established
`LocalFieldTheory.DiscreteValuationField` namespace because the same value
group is used by the valuation API; their implementation has no valued-field
hypotheses.
-/
set_option autoImplicit false
namespace LocalFieldTheory.DiscreteValuationField
/-- The subgroup of `Multiplicative ℤ` consisting of elements whose additive
integer is divisible by `d`. -/
def integerMultipleSubgroup (d : ℤ) : Subgroup (Multiplicative ℤ) where
  carrier := {n | d ∣ Multiplicative.toAdd n}
  one_mem' := by
    change d ∣ (0 : ℤ)
    exact dvd_zero d
  mul_mem' := by
    intro x y hx hy
    change d ∣ Multiplicative.toAdd (x * y)
    rw [toAdd_mul]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change d ∣ Multiplicative.toAdd x⁻¹
    rw [toAdd_inv]
    exact dvd_neg.mpr hx
end LocalFieldTheory.DiscreteValuationField
