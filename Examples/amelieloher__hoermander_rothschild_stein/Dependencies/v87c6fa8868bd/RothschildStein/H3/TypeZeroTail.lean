-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.H3.TypeZeroPrincipalValue
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.H3.Truncation
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.H3.SphereMaximum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Set
open scoped ENNReal
variable {N : ℕ} {G : HomogeneousGroup N}
/-- The finite annular tail in the unit-ball principal-value decomposition. -/
def typeZeroUnitTail (ν k : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  {x | 1 ≤ ν x ∧ ν x ≤ 2}.indicator (fun x => (1 - radialCutoff (ν x)) * k x)
/-- The annular tail is bounded by the actual unit-sphere kernel seminorm. -/
theorem TypeZero.unitTail_norm_le {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k) (x : Fin N → ℝ) :
    ‖typeZeroUnitTail ν k x‖ ≤ kernelSphereBound ν k := by
  have hΛ := (kernelSphereBound_continuous ν.gauge hk.smooth.continuousOn).1
  by_cases hx : x ∈ {y | 1 ≤ ν y ∧ ν y ≤ 2}
  · rw [typeZeroUnitTail, indicator_of_mem hx, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (radialCutoff_bounds (ν x)).2), Real.norm_eq_abs]
    have hx0 : x ≠ 0 := by
      intro he
      subst x
      have hz := (ν.gauge.2.2.1 0).mpr rfl
      change 1 ≤ ν 0 ∧ ν 0 ≤ 2 at hx
      linarith
    have hb := kernelSphereBound_homogeneous ν.gauge hk.smooth.continuousOn
      hk.homogeneous x hx0
    have hp : (ν x) ^ (-(G.homogeneousDimension : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx.1 (neg_nonpos.mpr (Nat.cast_nonneg _))
    have hbk : |k x| ≤ kernelSphereBound ν k := by
      apply hb.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hΛ
    calc
      (1 - radialCutoff (ν x)) * |k x| ≤ 1 * |k x| :=
        mul_le_mul_of_nonneg_right (by linarith [(radialCutoff_bounds (ν x)).1]) (abs_nonneg _)
      _ ≤ kernelSphereBound ν k := by simpa only [one_mul] using hbk
  · rw [typeZeroUnitTail, indicator_of_notMem hx, norm_zero]
    exact hΛ
end RothschildStein.H3
