/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gaussian integrals on `ℝ^d` for the local limit theorem

The Gaussian integral `∫_{ℝ^d} e^{-b|θ|²} = (π/b)^{d/2}` as a product of one-dimensional
ones, the second and fourth moments `∫ |θ|^{2m} e^{-a|θ|²} ≤ K a^{-(d+2m)/2}` by domination
with a Gaussian of half the rate, and the tail
`∫_{θ ∉ G} e^{-n|θ|²/(2d)} = O(n^{-(d+2)/2})` off the Gaussian region
`G = {θ : |θᵢ| ≤ π/2}`, where `|θ|² ≥ π²/4`.
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.LocalCLT
open ContinuousTime
variable {d : ℕ}
end LatticeProb.LocalCLT
end
