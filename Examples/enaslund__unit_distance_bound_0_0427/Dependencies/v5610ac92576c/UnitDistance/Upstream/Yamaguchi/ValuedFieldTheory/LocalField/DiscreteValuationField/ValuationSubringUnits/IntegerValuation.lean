/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.Arithmetic
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Integer valuations induced by `ℤᵐ⁰`-valued valuations

This file constructs the sign-normalized integer valuation on field units and
proves the elementary formulas for powers and natural-number denominators.
-/
noncomputable section
universe u
open WithZero
open scoped NNReal WithZero
namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation
variable {K : Type u} [Field K]
/-- The integer-valued multiplicative valuation attached to a
`ℤᵐ⁰`-valued field valuation.  The sign convention is normalized so that a
uniformizer of value `exp (-1)` has integer value `1`. -/
noncomputable def ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    MultiplicativeIntegerValuation Kˣ where
  val x := -WithZero.log (v (x : K))
  map_one := by
    simp
  map_mul x y := by
    have hx : v (x : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
    have hy : v (y : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 y.ne_zero
    change
      -WithZero.log (v ((x : K) * (y : K))) =
        -WithZero.log (v (x : K)) + -WithZero.log (v (y : K))
    rw [v.map_mul, WithZero.log_mul hx hy]
    ring
/-- Establishes the identity `(ofWithZeroValuation v).val x = -WithZero.log (v (x : K))`. -/
@[simp] theorem ofWithZeroValuation_val
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) :
    (ofWithZeroValuation v).val x = -WithZero.log (v (x : K)) :=
  rfl
end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
