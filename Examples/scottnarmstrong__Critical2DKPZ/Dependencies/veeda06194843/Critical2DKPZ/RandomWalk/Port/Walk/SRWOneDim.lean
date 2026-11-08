/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.OneDim
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # One-dimensional simple and lazy walk kernels

Two simple walk steps give a lazy step after dividing space by two; consequently
the simple walk kernel is bounded by `√2 / √(n+1)` at every site. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
/-- The `ℓ¹` norm of a one-dimensional site is the absolute value. -/
theorem graphNorm_one (a : ℤ) : graphNorm (![a] : Site 1) = a.natAbs := by
  simp [graphNorm]
end LatticeProb
end
