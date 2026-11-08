/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.KernelCalculusIncrement
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiSlab
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise bounds for the recentred kernel and the covariance

For abstract functions `K` (order `-3` with increments of order `-4`, time support `|t| ≤ 1`)
and `Q` (order `-1`, time support `|t| ≤ 2`) we bound, in terms of centred powers
`singularPow`,

* the recentred kernel `δK(z, w) = K(z - w) - K(-w)`, with and without a Hölder gain
  `s(z)^θ`;
* the covariance at a flipped argument, `|Q(w - u)| ≤ 2 B s(u - w)⁻¹`;
* the square and the cube of the covariance, the square with a loss `δ` of the exponent.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.18 and p. 167--168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
/-- Trivial bound for the recentred kernel. -/
theorem abs_dK_le {K : SpaceTime → ℝ} {B : ℝ}
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    {z w : SpaceTime} (hz : 0 < torusParabolicSize (z - w))
    (h0 : 0 < torusParabolicSize (0 - w)) :
    |K (z - w) - K (-w)| ≤ B * (singularPow 3 z w + singularPow 3 0 w) := by
  have h1 := hK _ hz
  have h2 := hK (0 - w) h0
  rw [zero_sub] at h2
  have e : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by
    simp [singularPow]
  rw [e]
  have e' : singularPow 3 z w = torusParabolicSize (z - w) ^ (-(3 : ℝ)) := by
    simp [singularPow]
  rw [e']
  calc |K (z - w) - K (-w)| ≤ |K (z - w)| + |K (-w)| := abs_sub _ _
    _ ≤ _ := by linarith
end RegularityStructures
end
