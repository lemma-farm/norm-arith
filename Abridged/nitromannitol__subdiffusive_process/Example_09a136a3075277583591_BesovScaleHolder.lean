module

public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_09a136a3075277583591_BesovScaleHolder ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Extended scale Hölder estimates

An extended-valued infinite-sum form of Hölder suitable for the exact Besov
scale aggregation.  Unlike the `NNReal` summability API, this remains valid
when either norm is infinite.
-/
namespace SubdiffusiveProcess.Section9
open scoped BigOperators ENNReal
/-- Hölder for `ENNReal` infinite sums, with no finiteness premise. -/
theorem ennrealTsum_mul_le_Lp_mul_Lq {ι : Type*} (f g : ι → ℝ≥0∞)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤
      (∑' i, f i ^ p) ^ p⁻¹ * (∑' i, g i ^ q) ^ q⁻¹ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  refine (ENNReal.inner_le_Lp_mul_Lq S f g hpq).trans ?_
  apply mul_le_mul
  · simpa only [one_div] using
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum S) (inv_nonneg.mpr hpq.pos.le)
  · simpa only [one_div] using
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum S) (inv_nonneg.mpr hpq.symm.pos.le)
  · exact bot_le
  · exact bot_le
end SubdiffusiveProcess.Section9
