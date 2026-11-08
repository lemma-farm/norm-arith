/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.SemigroupTestTreesChainIntegral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chain diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`

`i3PsiChain_bound_global`: for kernels `K, Q` with `|K| ≤ B s^(-3)`, `K = 0` for `|t| > 1`,
`|Q| ≤ B s^(-1)` (no support condition on `Q`), all `z, z'` with `z, z', z - z'` away from the
origin, and `D` bounding `s(w - v)` on the slab `|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`,
`|∫∫ chain| ≤ C D^δ (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`.
There is no smallness assumption on `z, z'`: the recentred kernels `K(z - ·) - K(-·)` vanish
outside the slab, and on the slab `Q(w - v)² ≤ B² D^δ s(w - v)^(-2-δ)`.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
theorem dK_eq_zero_of_abs_lt {K : SpaceTime → ℝ} (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    {z w : SpaceTime} (hw : |z.1| + 1 < |w.1|) : K (z - w) - K (-w) = 0 := by
  have e1 : K (z - w) = 0 := by
    apply hKs
    have : (z - w).1 = z.1 - w.1 := rfl
    rw [this]
    have h := abs_sub_abs_le_abs_sub w.1 z.1
    rw [abs_sub_comm w.1 z.1] at h
    linarith
  have e2 : K (-w) = 0 := by
    apply hKs
    have : (-w).1 = -w.1 := rfl
    rw [this, abs_neg]
    linarith [abs_nonneg z.1]
  rw [e1, e2, sub_zero]
end RegularityStructures
end
