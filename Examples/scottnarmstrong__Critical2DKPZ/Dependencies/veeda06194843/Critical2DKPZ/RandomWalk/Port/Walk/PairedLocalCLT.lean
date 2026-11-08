/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedMultiplier
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedOffIntegral
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.PairedGaussMoments
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The local central limit theorem on `ℤ^d`

**The paired local limit theorem** `|p_n(x) + p_{n+1}(x) - 2 ctGauss d n x| ≤ C n^{-(d+2)/2}`
for `n ≥ 1`, uniformly in `x` (`exists_abs_srwHeat_add_succ_sub_le`), where
`ctGauss d n x = (d/(2πn))^{d/2} e^{-d|x|²/(2n)}`, and its parity form
`|p_n(x) - 2 ctGauss d n x| ≤ C n^{-(d+2)/2}` at the sites of the parity of `n`
(`exists_abs_srwHeat_sub_le`), Lawler–Limic, *Random Walk: A Modern Introduction*, Theorem
2.1.3. The proof writes `(2π)^d(p_n + p_{n+1} - 2 ctGauss)` as the integral over the Gaussian
region of the difference of the paired multiplier and twice the Gaussian, plus the torus integral
off the Gaussian region, minus the Gaussian off it, and bounds the three.
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace LatticeProb.LocalCLT
open ContinuousTime
variable {d : ℕ}
end LatticeProb.LocalCLT
end
