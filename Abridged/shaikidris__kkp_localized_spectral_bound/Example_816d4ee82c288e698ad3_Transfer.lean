module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Fin.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Sequences
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Order.Compact

-- ==== Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.Basic.Inner ====
public section
/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
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
/-- The real Frobenius pairing `⟨B, C⟩ = tr(Bᵀ C)`. -/
def inner [Fintype n] (B C : Matrix n n ℝ) : ℝ :=
  (Bᵀ * C).trace
section Inner
variable [Fintype n]

end Inner
/-! ### N08 — Entrywise positive part -/
end BN

end
end

-- ==== Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.CP.Basic ====
public section
/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
@[expose] public section
/-!
# Completely positive matrices

A real matrix is completely positive if it is a finite sum of rank-one
matrices `vecMulVec p p` with entrywise nonnegative `p`.
-/
open Matrix
namespace BN
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- A real matrix is completely positive if it is a sum of outer products of
entrywise nonnegative vectors. -/
def IsCompletelyPositive (C : Matrix n n ℝ) : Prop :=
  ∃ (q : ℕ) (p : Fin q → n → ℝ),
    (∀ a i, 0 ≤ p a i) ∧ C = ∑ a, vecMulVec (p a) (p a)
end BN

end
end

-- ==== Examples.shaikidris__kkp_localized_spectral_bound.Examples.Example_816d4ee82c288e698ad3_Transfer ====
/-
Local exploratory transfer, generated with Codex on 2026-10-13.
Imports the Apache-2.0 BN development by Shengtong Zhang and collaborators.
Upstream source is unmodified; see ../upstream/LICENSE and the upstream metadata ../upstream/formalization.yaml.
-/
@[expose] public section
/-! A general scalar-certificate transfer. The certificate is an explicit premise;
this module does not yet formalize Bradač's edge-clique producer. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix BN
open scoped Matrix
namespace LocalBN
variable {n : Type*} [Fintype n] [DecidableEq n]
set_option linter.unusedVariables false in
/-- Factorwise passage of a homogeneous scalar certificate to CP matrices. -/
theorem cpPairing {W C : Matrix n n ℝ}
    (hscalar : ∀ y : n → ℝ, (∀ i, 0 ≤ y i) →
      BN.inner W (vecMulVec y y) ≤ (∑ i, y i) ^ 2)
    (hC : IsCompletelyPositive C) 
    (h_BN_inner_sum : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {ι : Type} (s : Finset ι) (B : Matrix V V ℝ)
      (C : ι → Matrix V V ℝ), BN.inner B (∑ a ∈ s, C a) = ∑ a ∈ s, BN.inner B (C a))
    (h_BN_inner_one_vecMulVec : ∀ {V : Type u_1} [inst : Fintype V] (p : V → ℝ),
      BN.inner ((Matrix.of : (V → V → ℝ) → Matrix V V ℝ) fun (x x_1 : V) ↦ 1) (Matrix.vecMulVec p p) =
        (∑ i : V, p i) ^ 2)
    :
    BN.inner W C ≤ BN.inner (of fun _ _ => (1 : ℝ)) C := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  rw [h_BN_inner_sum Finset.univ W (fun a => vecMulVec (p a) (p a))]
  rw [h_BN_inner_sum Finset.univ (of fun _ _ => (1 : ℝ))
    (fun a => vecMulVec (p a) (p a))]
  simp_rw [h_BN_inner_one_vecMulVec]
  exact Finset.sum_le_sum fun a _ => hscalar (p a) (hp a)
end LocalBN
