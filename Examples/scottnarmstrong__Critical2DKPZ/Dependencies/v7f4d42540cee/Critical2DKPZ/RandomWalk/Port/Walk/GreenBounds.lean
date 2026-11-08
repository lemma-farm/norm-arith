/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.Moment
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Bounds for coordinate-schedule averages

A Chernoff bound on coordinate counts controls the schedule average of the product
of inverse square roots by a constant times `r^{-d/2}`. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
variable {d : ℕ}
/-! ### The schedule average of `∏_i (N_i+1)^{-1/2}` -/
end LatticeProb
end
