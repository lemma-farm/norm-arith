/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.SingularConvolutionLayer
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise inequalities for parabolic powers

The Young-type inequalities (10.37a)--(10.37b) of [Hai14] for the parabolic size
`s = torusParabolicSize` on space-time, together with the quasi-triangle inequalities used
throughout the kernel calculus (`s(u + h) ≤ 4 (s u + s h)`, `s(-w) ≤ 2 s w`) and
almost-everywhere positivity of `s`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37), p. 168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
theorem torusParabolicSize_neg_le_two_mul (w : SpaceTime) :
    torusParabolicSize (-w) ≤ 2 * torusParabolicSize w := by
  unfold torusParabolicSize
  change √|(-w.1)| + torusSpatialNorm (-w.2) ≤ 2 * (√|w.1| + torusSpatialNorm w.2)
  rw [abs_neg]
  nlinarith [torusSpatialNorm_neg_le w.2, Real.sqrt_nonneg |w.1|, torusSpatialNorm_nonneg w.2]
theorem torusParabolicSize_add_le_four_mul (u h : SpaceTime) :
    torusParabolicSize (u + h) ≤ 4 * (torusParabolicSize u + torusParabolicSize h) := by
  have := torusParabolicSize_sub_le (u + h) u
  simpa [add_sub_cancel_left, add_comm] using this
theorem torusParabolicSize_sub_le_eight_mul (z w : SpaceTime) :
    torusParabolicSize (z - w) ≤ 8 * (torusParabolicSize z + torusParabolicSize w) := by
  have h1 := torusParabolicSize_sub_le (z - w) z
  have h2 := torusParabolicSize_neg_le_two_mul w
  have h3 : z - w - z = -w := by abel
  rw [h3] at h1
  have := torusParabolicSize_nonneg z
  have := torusParabolicSize_nonneg w
  nlinarith
theorem ae_torusParabolicSize_pos_spaceTime :
    ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize w := by
  rw [ae_iff]
  have h := Phi43.volume_torusParabolicBall_le_global (le_refl (0 : ℝ))
  have h0 : volume {z : SpaceTime | torusParabolicSize z ≤ 0} = 0 :=
    nonpos_iff_eq_zero.1 (by simpa using h)
  refine measure_mono_null ?_ h0
  intro w hw
  exact not_lt.1 hw
theorem ae_torusParabolicSize_sub_pos (z : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize (z - w) :=
  (measurePreserving_sub_left_spaceTime z).quasiMeasurePreserving.ae
    ae_torusParabolicSize_pos_spaceTime
private theorem rpow_neg_mul_rpow_neg_le {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : x ^ (-a) * y ^ (-b) ≤ x ^ (-(a + b)) + y ^ (-(a + b)) := by
  have hx' : 0 ≤ x ^ (-(a + b)) := Real.rpow_nonneg hx.le _
  have hy' : 0 ≤ y ^ (-(a + b)) := Real.rpow_nonneg hy.le _
  rcases le_total x y with h | h
  · have h1 : y ^ (-b) ≤ x ^ (-b) := Real.rpow_le_rpow_of_nonpos hx h (neg_nonpos.2 hb)
    have h2 : x ^ (-a) * x ^ (-b) = x ^ (-(a + b)) := by
      rw [← Real.rpow_add hx]; ring_nf
    calc
      x ^ (-a) * y ^ (-b) ≤ x ^ (-a) * x ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx.le _)
      _ = x ^ (-(a + b)) := h2
      _ ≤ _ := le_add_of_nonneg_right hy'
  · have h1 : x ^ (-a) ≤ y ^ (-a) := Real.rpow_le_rpow_of_nonpos hy h (neg_nonpos.2 ha)
    have h2 : y ^ (-a) * y ^ (-b) = y ^ (-(a + b)) := by
      rw [← Real.rpow_add hy]; ring_nf
    calc
      x ^ (-a) * y ^ (-b) ≤ y ^ (-a) * y ^ (-b) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy.le _)
      _ = y ^ (-(a + b)) := h2
      _ ≤ _ := le_add_of_nonneg_left hx'
/-- [Hai14, (10.37a)]: `s(z)^(-a) s(z̄)^(-b) ≤ s(z)^(-a-b) + s(z̄)^(-a-b)` for `a, b ≥ 0`. -/
theorem torusParabolicSize_rpow_neg_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {z z' : SpaceTime} (hz : 0 < torusParabolicSize z) (hz' : 0 < torusParabolicSize z') :
    torusParabolicSize z ^ (-a) * torusParabolicSize z' ^ (-b) ≤
      torusParabolicSize z ^ (-(a + b)) + torusParabolicSize z' ^ (-(a + b)) :=
  rpow_neg_mul_rpow_neg_le hz hz' ha hb
end RegularityStructures
end
