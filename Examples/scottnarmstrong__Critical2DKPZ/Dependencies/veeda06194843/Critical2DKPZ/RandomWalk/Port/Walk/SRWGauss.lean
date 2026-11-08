/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.Decomp
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.GreenBounds
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
Two elementary ingredients of the Gaussian bound on the lattice kernel.

The first is that a schedule of `r` coordinate choices distributes exactly `r`
steps among the coordinates.  The second is Sedrakyan's form of the Cauchy
inequality, which turns a product of one-dimensional Gaussian factors, one for
each coordinate and each with its own number of steps, into a single Gaussian
factor in the `ℓ¹` norm of the site and the total number of steps.
-/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
variable {d : ℕ}
end LatticeProb
end
