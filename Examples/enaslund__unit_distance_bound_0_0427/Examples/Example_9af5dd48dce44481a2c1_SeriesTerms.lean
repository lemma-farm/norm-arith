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
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalProduct
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
Defines the logarithm and exponential series terms and proves the valuation estimates used in
their convergence arguments.
-/
open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation
variable {K : Type u} [Field K]
/-- The integer valuation attached to a nonarchimedean `ℤᵐ⁰`-valuation is
bounded below by the minimum under addition. -/
theorem ofWithZeroValuation_val_add_ge_min
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min ((ofWithZeroValuation v).val (Units.mk0 x hx))
        ((ofWithZeroValuation v).val (Units.mk0 y hy)) ≤
      (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
  have hsum : v (x + y) ≤ max (v x) (v y) :=
    map_add_le_max v x y
  by_cases hxyv : v x ≤ v y
  · have hsum_y : v (x + y) ≤ v y := by
      simpa [max_eq_right hxyv] using hsum
    have hsum_ne : v (x + y) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hxy
    have hy_ne : v y ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hy
    have hlog :
        WithZero.log (v (x + y)) ≤ WithZero.log (v y) :=
      (WithZero.log_le_log hsum_ne hy_ne).2 hsum_y
    have hy_le_sum :
        (ofWithZeroValuation v).val (Units.mk0 y hy) ≤
          (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
      simp [ofWithZeroValuation_val]
      linarith
    exact le_trans (min_le_right _ _) hy_le_sum
  · have hyxv : v y ≤ v x := le_of_not_ge hxyv
    have hsum_x : v (x + y) ≤ v x := by
      simpa [max_eq_left hyxv] using hsum
    have hsum_ne : v (x + y) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hxy
    have hx_ne : v x ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hx
    have hlog :
        WithZero.log (v (x + y)) ≤ WithZero.log (v x) :=
      (WithZero.log_le_log hsum_ne hx_ne).2 hsum_x
    have hx_le_sum :
        (ofWithZeroValuation v).val (Units.mk0 x hx) ≤
          (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
      simp [ofWithZeroValuation_val]
      linarith
    exact le_trans (min_le_left _ _) hx_le_sum
end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
