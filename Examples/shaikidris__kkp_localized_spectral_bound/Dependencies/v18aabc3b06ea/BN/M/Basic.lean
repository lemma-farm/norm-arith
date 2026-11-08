/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.Basic.Inner
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.CP.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Lattice
@[expose] public section
/-!
# The matrix `M(X)` of `eq:matrix`

For a real matrix `X`,
`M X = X ⊙ X + ∑_{i<j} (if X i j < 0 then (X i j)² else 0) • vecMulVec (e i - e j) (e i - e j)`.
When `X` is positive semidefinite this is PSD and entrywise nonnegative.
-/
namespace BN
open Matrix Finset
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
noncomputable section
/-! ### MX01 — definition of `M` -/
end
end BN
