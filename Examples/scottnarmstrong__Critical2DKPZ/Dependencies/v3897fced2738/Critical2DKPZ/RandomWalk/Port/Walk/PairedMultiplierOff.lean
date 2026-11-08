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
# The paired Fourier multiplier off the Gaussian region

Off the Gaussian region of the torus, where one coordinate of `θ` is within `π/2` of `0` and
another is not, `|φ(θ)| ≤ 1 - 1/d`; where every coordinate is within `π/2` of `±π`,
`φ ≤ 0`, `|φ(θ)| ≤ e^{-2|ψ|²/(π²d)}` and `0 ≤ 1 + φ(θ) ≤ |ψ|²/(2d)` with
`ψᵢ = π - |θᵢ|`, so the factor `1 + φ` of the paired multiplier vanishes at the antipode.
Together these give the majorant `offBound` of `φⁿ(1 + φ)` (`abs_charFn_pow_mul_le_offBound`).
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.LocalCLT
open ContinuousTime
variable {d : ℕ}
end LatticeProb.LocalCLT
end
