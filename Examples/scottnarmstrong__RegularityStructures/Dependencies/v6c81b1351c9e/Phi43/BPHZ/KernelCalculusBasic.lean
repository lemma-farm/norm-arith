/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.Phi43.BPHZ.SingularConvolutionLayer
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
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
theorem torusParabolicSize_sub_le_eight_mul (z w : SpaceTime) :
    torusParabolicSize (z - w) ≤ 8 * (torusParabolicSize z + torusParabolicSize w) := by
  have h1 := torusParabolicSize_sub_le (z - w) z
  have h2 := torusParabolicSize_neg_le_two_mul w
  have h3 : z - w - z = -w := by abel
  rw [h3] at h1
  have := torusParabolicSize_nonneg z
  have := torusParabolicSize_nonneg w
  nlinarith
end RegularityStructures
end
