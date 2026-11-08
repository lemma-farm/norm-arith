/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.SRWGauss
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.SRWDecomp
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.S1Gauss
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
The Gaussian upper bound on the simple random walk kernel.

Each coordinate of the walk, run for `N_i` of the `r` steps, contributes a
one-dimensional factor bounded by `3 (N_i+1)^{-1/2} exp(-x_i^2 / (8(N_i+2)))`.
The exponents add, and Sedrakyan's inequality turns the sum
`∑_i x_i^2/(N_i+2)` into `|x|_1^2 / ∑_i (N_i+2) = |x|_1^2 / (r + 2d)`, which no
longer depends on the schedule.  The Gaussian factor therefore comes out of the
schedule average, and what is left is the average of `∏_i (N_i+1)^{-1/2}`, which
is of order `r^{-d/2}`.  The bound is in the `ℓ¹` norm, hence stronger than the
usual Euclidean form.
-/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
variable {d : ℕ}
end LatticeProb
end
