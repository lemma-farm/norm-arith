/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The one-dimensional lazy random walk kernel

The kernel `p_m(k) = 4^{-m} binom(2m,m+k)` describes a walk that stays put with
probability one half and moves in each direction with probability one quarter. It is
symmetric and unimodal, has total mass one, and its maximum is at most `(m+1)^{-1/2}`. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
/-! ### Binomial coefficients with an integer lower index -/
end LatticeProb
end
