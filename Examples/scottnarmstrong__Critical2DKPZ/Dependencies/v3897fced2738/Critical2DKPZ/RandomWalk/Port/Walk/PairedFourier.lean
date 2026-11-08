/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.LocalCLT
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The paired heat kernel of the simple random walk in Fourier form

`p_n(x) + p_{n+1}(x)` is `(2π)^{-d}` times the torus integral of `χ_x φⁿ (1 + φ)`, where
`φ(θ) = d⁻¹ ∑ᵢ cos θᵢ` is the multiplier of one step and
`χ_x(θ) = ∏ₖ e^{iθₖxₖ}`. Pairing two consecutive times puts the factor `1 + φ` in the
integrand, which vanishes at the antipode `θ = (π, …, π)`; this is what lets the local limit
theorem avoid identifying the antipode contribution. The module also computes the Fourier
transform of the Gaussian, `∫_{ℝ^d} χ_x e^{-n|θ|²/(2d)} = (2π)^d ctGauss d n x`, as a
product of one-dimensional Gaussian integrals, and fixes the Gaussian region
`{θ : |θᵢ| ≤ π/2}` of the torus.
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.LocalCLT
open ContinuousTime
variable {d : ℕ}
end LatticeProb.LocalCLT
end
