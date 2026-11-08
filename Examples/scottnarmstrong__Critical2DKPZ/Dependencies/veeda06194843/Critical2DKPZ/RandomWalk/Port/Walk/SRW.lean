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
/-! # The simple random walk kernel and its parity constraint

Iterating the nearest-neighbour averaging operator from the unit atom at the origin
gives a kernel supported inside the graph-distance ball and on the parity class of time. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
variable {d : ℕ}
/-! ### The `ℓ¹` norm of a site -/
/-- The graph distance from the origin: the `ℓ¹` norm of a site. -/
def graphNorm {d : ℕ} (x : Site d) : ℕ := ∑ i, (x i).natAbs
noncomputable def srwHeat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => walkOp (srwHeat d j) x
end LatticeProb
namespace LatticeProb
open Finset
/-! ### The one-dimensional nearest-neighbour recursion -/
end LatticeProb
end
