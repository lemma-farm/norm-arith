/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.OneDim
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
A Gaussian off-diagonal bound for the one-dimensional lazy walk kernel `P1`.

Writing `p_m(k) = 4^{-m} binom(2m, m+k)`, the Pascal recurrence gives the exact
ratio of consecutive weights on the right half of the range,

  `p_m(k+1) / p_m(k) = (m - k) / (m + k + 1)`,

valid for `0 ≤ k ≤ m`.  Since `m + k + 1 ≤ 2(m + 1)` in that range, the ratio is
at most `1 - (2k+1) / (2(m+1))`, hence at most `exp(-(2k+1) / (2(m+1)))`.  The
increments `2k + 1` telescope to a square, `∑_{j<k} (2j+1) = k^2`, so multiplying
the bounds along `0, 1, …, k` yields

  `p_m(k) ≤ p_m(0) exp(-k^2 / (2(m+1)))`.

Outside the range the left-hand side vanishes, and the estimate is symmetric in
`k`, so it holds for every integer `k`.
-/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
end LatticeProb
end
