/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.GammaMomentSecond
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeWickCube
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2Field
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DifferenceMean
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.HairerCovarianceBounds
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramMultiSq
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Second moments of the recentred convolutions `v₂` and `v₃`

With `K = hairerKernelTorus N` and the increment `δK_{x,y}(w) = K(y - w) - K(x - w)`
(`hairerI2Psi2Kernel`), the entries of the structure-group element `Γ_{yx}` of the renormalised
model contain the recentred convolutions of [Hai14, Lemma 5.16]

* `v₂(x, y) = ∫ δK_{x,y}(w) :Ψ²:(w) dw` (`gammaWickSq`), degree `1 - 2κ`;
* `v₃(x, y) = ∫ δK_{x,y}(w) :Ψ³:(w) dw` (`gammaWickCube`), degree `1/2 - 3κ`.

For `d = s(y - x) ≤ 1`, uniformly in the regularisation `ε ∈ (0, 1]`, the base point and the
probability space:

* `gammaWickSq_second_moment_le`: `E v₂² ≤ C d^(2-δ)` for every `δ ∈ (0, 1]`;
* `gammaWickCube_second_moment_le`: `E v₃² ≤ C d^(1-δ)` for every `δ ∈ (0, 1]`.

The proofs combine `E[:Ψ²:(u) :Ψ²:(v)] = 2 Q_ε(u - v)²`, `E[:Ψ³:(u) :Ψ³:(v)] = 6 Q_ε(u - v)³`
with the covariance bound `|Q_ε| ≲ s⁻¹` and the principal pairing estimate
`i2Psi2LintBound_diag_sq` for `∬ |δK| |δK| s^(-e)` (exponent `e = 2, 3`).
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
/-- The recentred convolution `v₂(x, y) = ∫ (K(y - w) - K(x - w)) :Ψ²:(w) dw`. -/
def gammaWickSq {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ : Ω → SpaceTime → ℝ)
    (x y : SpaceTime) (ω : Ω) : ℝ :=
  ∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickSquare N ρ ε ξ ω w
end RegularityStructures.Phi43
end
public section
open MeasureTheory
universe u
namespace RegularityStructures.Phi43
open RegularityStructures
/-- A parabolic size at most `1` bounds the time displacement by `1`. -/
theorem gammaMoment_abs_time_le_one {t : ℝ} {z : SpaceTime} (h : torusParabolicSize z ≤ 1)
    (ht : t = z.1) : |t| ≤ 1 := by
  subst ht
  have h1 : √|z.1| ≤ 1 := by
    have := torusSpatialNorm_nonneg z.2
    unfold torusParabolicSize at h
    linarith
  exact Real.sqrt_le_one.1 h1
end RegularityStructures.Phi43
end
