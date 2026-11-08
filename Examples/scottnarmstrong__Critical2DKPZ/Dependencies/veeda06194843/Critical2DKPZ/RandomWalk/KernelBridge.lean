/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.SrwKernel
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.SRW
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Identifying the path sum with the recursive simple walk kernel

The four step labels enumerate the two signed coordinate directions. Splitting a
word at its final letter gives the same recursion as `LatticeProb.srwHeat`.
-/
@[expose] public section
namespace Critical2DKPZ
end Critical2DKPZ
