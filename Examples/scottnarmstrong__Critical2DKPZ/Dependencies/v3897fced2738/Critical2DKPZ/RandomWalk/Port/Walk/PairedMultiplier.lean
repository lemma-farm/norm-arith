/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The paired Fourier multiplier on the Gaussian region

On the Gaussian region `{θ : |θᵢ| ≤ π/2}` the multiplier `φ(θ) = d⁻¹ ∑ᵢ cos θᵢ`
is nonnegative, below `e^{-2|θ|²/(π²d)}`, and the Gaussian `e^{-|θ|²/(2d)}` up to `|θ|⁴`.
With the elementary bound `|aⁿ - bⁿ| ≤ n|a - b| max(a, b)^{n-1}` this makes the paired
multiplier `φⁿ(1 + φ)` twice the Gaussian `e^{-n|θ|²/(2d)}` up to
`K(n|θ|⁴ + |θ|²)e^{-cn|θ|²}` (`exists_abs_charFn_pow_mul_sub_le`).
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.LocalCLT
open ContinuousTime
variable {d : ℕ}
end LatticeProb.LocalCLT
end
