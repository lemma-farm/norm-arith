/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.Phi43.BPHZ.SemigroupTestProfile
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.Phi43.BPHZ.ChaosReductionIntegralWeights
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.Phi43.BPHZ.KernelCalculusBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chaos-reduction double integral for a semigroup test profile

For a semigroup test profile `g` at scale `lam` and base point `x` (see `SemigroupTestProfile`) and
real exponents `ζ, e > -5`,
`∫∫ |g u| |g v| s(u - x)^ζ s(u - v)^e ≤ C lam^(ζ+e)`
(`SemigroupTestProfile.integral_double_le`).  This is the analogue of
`chaosReduction_integral_left` with the compactly supported test function replaced by a profile
with unbounded support, for which only a sup bound and moment bounds are available.

* For `e < 0` the inner integral over `v` is bounded uniformly in `u` by
  `SemigroupTestProfile.integral_mul_rpow_sub_le`.
* For `e ≥ 0` we use `s(u - v)^e ≤ 16^e (s(u - x)^e + s(v - x)^e)` and the moment bounds.
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
theorem torusParabolicSize_sub_rpow_le {e : ℝ} (he : 0 ≤ e) (u v x : SpaceTime) :
    torusParabolicSize (u - v) ^ e ≤
      16 ^ e * (torusParabolicSize (u - x) ^ e + torusParabolicSize (v - x) ^ e) := by
  have h8 := torusParabolicSize_sub_le_eight_mul (u - x) (v - x)
  rw [sub_sub_sub_cancel_right] at h8
  set a := torusParabolicSize (u - x) with ha
  set b := torusParabolicSize (v - x) with hb
  have ha0 : 0 ≤ a := torusParabolicSize_nonneg _
  have hb0 : 0 ≤ b := torusParabolicSize_nonneg _
  have hsum : a + b ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have hmax : max a b ^ e ≤ a ^ e + b ^ e := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg ha0 _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hb0 _)
  have hle : torusParabolicSize (u - v) ≤ 16 * max a b := by
    have := le_max_left a b
    linarith
  calc torusParabolicSize (u - v) ^ e ≤ (16 * max a b) ^ e :=
        Real.rpow_le_rpow (torusParabolicSize_nonneg _) hle he
    _ = 16 ^ e * max a b ^ e := Real.mul_rpow (by norm_num) (le_max_of_le_left ha0)
    _ ≤ 16 ^ e * (a ^ e + b ^ e) :=
        mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)
namespace SemigroupTestProfile
variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}
end SemigroupTestProfile
end RegularityStructures
end
