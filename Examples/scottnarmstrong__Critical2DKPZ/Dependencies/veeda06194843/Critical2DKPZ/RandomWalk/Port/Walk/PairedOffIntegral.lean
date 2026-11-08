/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedMultiplierOff
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The torus integral of the majorant off the Gaussian region

`∫_{[-π,π]^d} offBound d n = O(n^{-(d+2)/2})` (`exists_integral_offBound_le`). The constant
part `2(1 - 1/d)ⁿ` of the majorant decays faster than any power. Its second part is a sum of
products over the coordinates, so its integral is `A B^{d-1}/2` with one-dimensional integrals
`A`, `B` of `1_{|t| > π/2} e^{-b(π - |t|)²}` (weighted by `(π - |t|)²` for `A`),
`b = 2n/(π²d)`; bounding that factor by the two translated Gaussians
`e^{-b(t - π)²} + e^{-b(t + π)²}` gives `A = O(b^{-3/2})` and `B = O(b^{-1/2})`.
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.LocalCLT
open ContinuousTime
variable {d : ℕ}
end LatticeProb.LocalCLT
end
