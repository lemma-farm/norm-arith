/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
@[expose] public section
/-!
# Frobenius pairing, entrywise positive part, and the Schur product

This file records the real Frobenius inner product `⟨B, C⟩ = tr(Bᵀ C)`, the
entrywise positive part of a matrix, the rank-one Laplacian
`vecMulVec (e i - e j) (e i - e j)`, and the Schur product theorem for real
positive semidefinite matrices.
-/
namespace BN
open Matrix
open scoped Matrix
variable {m n : Type*}
/-! ### N06 — Frobenius pairing -/
section Inner
variable [Fintype n]
end Inner
/-! ### N08 — Entrywise positive part -/
def e [DecidableEq n] (k : n) : n → ℝ :=
  Pi.single k 1
end BN
