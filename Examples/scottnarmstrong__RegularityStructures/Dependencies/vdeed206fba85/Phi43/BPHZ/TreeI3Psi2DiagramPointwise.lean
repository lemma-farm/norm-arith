/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2DiagramLeaves
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3PsiChainBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise majorants for the diagrams of `I(Ψ³)Ψ²`

Bounds of the covariance entries by centred powers, `|Q(c - w)| ≤ B s(c - w)^(-1)`, its square
(with and without a loss `δ` of the exponent, the latter on the slab `|t| ≤ 4`), and the time
slab on which the recentred kernel `δK(z, ·)` lives.
-/
public section
open MeasureTheory
namespace RegularityStructures
/-- If `s(z) ≤ 1` then `|z.1| ≤ 1`. -/
theorem abs_fst_le_one_of_size_le_one {z : SpaceTime} (hz : torusParabolicSize z ≤ 1) :
    |z.1| ≤ 1 := by
  have h1 : √|z.1| ≤ 1 := by
    have := torusSpatialNorm_nonneg z.2
    unfold torusParabolicSize at hz
    linarith
  have := Real.sqrt_le_iff.1 h1
  linarith [this.2]
theorem abs_Q_sq_le_singularPow_loss {Q : SpaceTime → ℝ} {B δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {c w : SpaceTime} (h : 0 < torusParabolicSize (c - w)) (h4 : |(c - w).1| ≤ 4) :
    |Q (c - w)| ^ 2 ≤ B ^ 2 * 3 ^ δ * singularPow (2 + δ) c w :=
  abs_Q_sq_le_of_abs_le_four hδ hQ h h4
/-- The time coordinate of `c - w` is at most `3` when `|c.1| ≤ 1` and `|w.1| ≤ 2`. -/
theorem abs_sub_fst_le_four {c w : SpaceTime} (hc : |c.1| ≤ 1) (hw : |w.1| ≤ 2) :
    |(c - w).1| ≤ 4 := by
  have : (c - w).1 = c.1 - w.1 := rfl
  rw [this]
  exact (abs_sub _ _).trans (by linarith)
/-- Evenness turns `Q(w - c)` into `Q(c - w)`. -/
theorem Q_sub_comm {Q : SpaceTime → ℝ} (hQe : ∀ x, Q (-x) = Q x) (a b : SpaceTime) :
    Q (a - b) = Q (b - a) := by
  rw [← hQe (b - a), neg_sub]
end RegularityStructures
end
