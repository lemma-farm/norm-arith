/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Units
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace LocalFieldTheory
/-!
# Integer-valued norm data

This file contains the norm-subgroup lemmas used in local CFT from an abstract
integer-valued multiplicative valuation and a norm homomorphism satisfying the
standard valuation formula.
-/
noncomputable section
universe u v
namespace DiscreteValuationField
/-- A multiplicative group valuation with values in additive integers. -/
structure MultiplicativeIntegerValuation (G : Type u) [Group G] where
  /-- The integer valuation of a group element. -/
  val : G → ℤ
  /-- The identity has valuation zero. -/
  map_one : val 1 = 0
  /-- Valuation turns multiplication into integer addition. -/
  map_mul : ∀ x y : G, val (x * y) = val x + val y
namespace MultiplicativeIntegerValuation
variable {G : Type u} [Group G] (V : MultiplicativeIntegerValuation G)
/-- Establishes the identity `V.val (1 : G) = 0`. -/
@[simp] theorem val_one : V.val (1 : G) = 0 :=
  V.map_one
/-- `val` satisfies the multiplication formula `V.val (x * y) = V.val x + V.val y`. -/
@[simp] theorem val_mul (x y : G) :
    V.val (x * y) = V.val x + V.val y :=
  V.map_mul x y
/-- The integer-valued valuation as a multiplicative homomorphism to the
additive group of integers written multiplicatively. -/
def valuationHom : G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (V.val x)
  map_one' := by
    simp [V.val_one]
  map_mul' x y := by
    rw [V.val_mul, ofAdd_add]
/--
The defining evaluation formula for `valuationHom` is `V.valuationHom x = Multiplicative.ofAdd
(V.val x)`.
-/
@[simp] theorem valuationHom_apply (x : G) :
    V.valuationHom x = Multiplicative.ofAdd (V.val x) :=
  rfl
/-- Characterizes `x ∈ V.valuationHom.ker` by the equivalent condition `V.val x = 0`. -/
theorem mem_valuationHom_ker_iff (x : G) :
    x ∈ V.valuationHom.ker ↔ V.val x = 0 := by
  change V.valuationHom x = 1 ↔ V.val x = 0
  rw [V.valuationHom_apply]
  constructor
  · intro hx
    exact Multiplicative.ofAdd.injective (by simpa using hx)
  · intro hx
    rw [hx]
    simp
/-- `val` satisfies the inverse formula `V.val x⁻¹ = -V.val x`. -/
@[simp] theorem val_inv (x : G) :
    V.val x⁻¹ = -V.val x := by
  have h := V.map_mul x x⁻¹
  have h' : V.val x + V.val x⁻¹ = 0 := by
    simpa [V.map_one] using h.symm
  exact eq_neg_iff_add_eq_zero.2 (by simpa [add_comm] using h')
theorem val_inv_eq_zero_of_val_eq_zero {x : G} (hx : V.val x = 0) :
    V.val x⁻¹ = 0 := by
  rw [V.val_inv, hx, neg_zero]
def zeroSubgroup : Subgroup G where
  carrier := {x | V.val x = 0}
  one_mem' := by simp [V.map_one]
  mul_mem' := by
    intro x y hx hy
    change V.val (x * y) = 0
    rw [V.map_mul, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    exact V.val_inv_eq_zero_of_val_eq_zero hx
/-- Characterizes `x ∈ V.zeroSubgroup` by the equivalent condition `V.val x = 0`. -/
@[simp] theorem mem_zeroSubgroup_iff (x : G) :
    x ∈ V.zeroSubgroup ↔ V.val x = 0 :=
  Iff.rfl
/-- Establishes the identity `V.valuationHom.ker = V.zeroSubgroup`. -/
theorem valuationHom_ker_eq_zeroSubgroup :
    V.valuationHom.ker = V.zeroSubgroup := by
  ext x
  rw [V.mem_valuationHom_ker_iff, V.mem_zeroSubgroup_iff]
/-- The subgroup appearing in `(V.zeroSubgroup).Normal` is normal. -/
instance zeroSubgroup_normal : (V.zeroSubgroup).Normal := by
  rw [← V.valuationHom_ker_eq_zeroSubgroup]
  infer_instance
def IsUniformizer (ϖ : G) : Prop :=
  V.val ϖ = 1
structure UnitUniformizerDecomposition (ϖ x : G) where
  /-- The valuation-zero factor. -/
  unitPart : G
  /-- The unit factor has valuation zero. -/
  unit_mem : unitPart ∈ V.zeroSubgroup
  /-- The exponent of the chosen uniformizer. -/
  exponent : ℤ
  /-- Reconstruction from the unit factor and uniformizer power. -/
  eq_unit_mul_zpow : x = unitPart * ϖ ^ exponent
namespace UnitUniformizerDecomposition
variable {V : MultiplicativeIntegerValuation G} {ϖ x : G}
end UnitUniformizerDecomposition
end MultiplicativeIntegerValuation
/-- A norm-like homomorphism compatible with integer-valued valuations.

`residueDegree` is proof-attached data: it is the multiplier in
`valuation_formula`, not an independent field-extension invariant.  In the
usual discrete-valued application the source has a uniformizer, and evaluating
`valuation_formula` at that uniformizer uniquely determines this coefficient.
The generic group-level abstraction does not require a uniformizer, so it keeps
the coefficient together with the formula that certifies it. -/
structure ValuedNorm {G : Type u} {H : Type v} [Group G] [Group H]
    (vG : MultiplicativeIntegerValuation G)
    (vH : MultiplicativeIntegerValuation H) where
  /-- The multiplicative norm homomorphism. -/
  toHom : H →* G
  /-- The nonnegative scaling factor in the valuation formula. -/
  residueDegree : ℕ
  /-- Applying the norm scales valuation by the residue-degree factor. -/
  valuation_formula :
    ∀ x : H, vG.val (toHom x) = (residueDegree : ℤ) * vH.val x
end DiscreteValuationField
end
end LocalFieldTheory
