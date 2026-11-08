/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramInner
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The kernel increment and the covariance weights

`i2Psi2Increment K x y w = K(y - w) - K(x - w)` is the kernel `δK_x(y, w)` of [Hai14, (10.39)].
A covariance `Q` with `|Q u| ≤ B s(u)^(-1)` satisfies the flipped bound
`|Q(w - g)| ≤ 2 B s(g - w)^(-1)` (`abs_cov_flip_le`), and its square
`Q(w - g)² ≤ 4 B² s(g - w)^(-2)` (`sq_cov_flip_le`), so that it can be paired with the weights
of `TreeI2Psi2DiagramInner`, which are written with `s(g - w)`.
-/
@[expose] public section
namespace RegularityStructures
/-- The kernel increment `δK_x(y, w) = K(y - w) - K(x - w)` of [Hai14, (10.39)]. -/
def i2Psi2Increment (K : SpaceTime → ℝ) (x y w : SpaceTime) : ℝ :=
  K (y - w) - K (x - w)
end RegularityStructures
end
public section
namespace RegularityStructures
theorem torusParabolicSize_pos_of_sub_pos {a b : SpaceTime} (h : 0 < torusParabolicSize (a - b)) :
    0 < torusParabolicSize (b - a) := by
  have h2 := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at h2
  linarith
/-- `s(u)^(-e) ≤ 2^e s(-u)^(-e)`. -/
theorem torusParabolicSize_rpow_neg_le_flip {e : ℝ} (he : 0 ≤ e) {u : SpaceTime}
    (hu : 0 < torusParabolicSize (-u)) :
    torusParabolicSize u ^ (-e) ≤ 2 ^ e * torusParabolicSize (-u) ^ (-e) := by
  have h2 := torusParabolicSize_neg_le_two_mul u
  have hh : torusParabolicSize (-u) * 2⁻¹ ≤ torusParabolicSize u := by linarith
  have h1 : torusParabolicSize u ^ (-e) ≤ (torusParabolicSize (-u) * 2⁻¹) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hh (neg_nonpos.2 he)
  have h3 : (2⁻¹ : ℝ) ^ (-e) = 2 ^ e := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  rw [Real.mul_rpow hu.le (by norm_num), h3, mul_comm] at h1
  exact h1
theorem measurable_i2Psi2Increment {K : SpaceTime → ℝ} (hK : Measurable K) (x y : SpaceTime) :
    Measurable (i2Psi2Increment K x y) :=
  (hK.comp (measurable_const.sub measurable_id)).sub (hK.comp (measurable_const.sub measurable_id))
end RegularityStructures
end
