/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

Formalization of the opening display of Section 4 ("Channel estimates and the
scalar vacuum majorant") of Version 3.0 of the manuscript *SparseStack Is an
Optimal Oblivious Subspace Embedding*:

  "Block Cauchy--Schwarz gives
     ‖∑_k B_k A_k‖² ≤ ‖∑_k A_k^* A_k‖ ‖∑_k B_k B_k^*‖.
   This is the norm bound for the product of a block row and block column."

Only the Cauchy--Schwarz display is formalized here; the elementary
block-sparsity count of Section 2.3 is not part of this file.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator
namespace SparseStackV3.BlockCS
noncomputable section
variable {K p r t : ℕ}
/-- The **block column** assembled from a family `A : Fin K → Matrix (Fin r) (Fin p) ℝ`
of blocks: the matrix on the index type `Fin K × Fin r` whose `(k, x)`-th row is the
`x`-th row of the `k`-th block.  This is the "block column" of the manuscript's
Section 4 opening display. -/
def blockCol (A : Fin K → Matrix (Fin r) (Fin p) ℝ) :
    Matrix (Fin K × Fin r) (Fin p) ℝ :=
  Matrix.of fun x i => A x.1 x.2 i
/-- The **block row** assembled from a family `B : Fin K → Matrix (Fin t) (Fin r) ℝ`
of blocks: the matrix with columns indexed by `Fin K × Fin r` whose `(k, x)`-th column
is the `x`-th column of the `k`-th block.  This is the "block row" of the manuscript's
Section 4 opening display. -/
def blockRow (B : Fin K → Matrix (Fin t) (Fin r) ℝ) :
    Matrix (Fin t) (Fin K × Fin r) ℝ :=
  Matrix.of fun y x => B x.1 y x.2
@[simp] lemma blockCol_apply (A : Fin K → Matrix (Fin r) (Fin p) ℝ)
    (x : Fin K × Fin r) (i : Fin p) : blockCol A x i = A x.1 x.2 i := rfl
@[simp] lemma blockRow_apply (B : Fin K → Matrix (Fin t) (Fin r) ℝ)
    (y : Fin t) (x : Fin K × Fin r) : blockRow B y x = B x.1 y x.2 := rfl
/-- The product of the block row and the block column is the sum `∑_k B_k A_k`
appearing on the left-hand side of the manuscript's display. -/
theorem blockRow_mul_blockCol (A : Fin K → Matrix (Fin r) (Fin p) ℝ)
    (B : Fin K → Matrix (Fin t) (Fin r) ℝ) :
    blockRow B * blockCol A = ∑ k, B k * A k := by
  ext y i
  simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
/-- The Gram matrix of the block column is the sum `∑_k A_k^* A_k` appearing on the
right-hand side of the manuscript's display (for real matrices the adjoint `A^*` is
the transpose). -/
theorem transpose_blockCol_mul_blockCol (A : Fin K → Matrix (Fin r) (Fin p) ℝ) :
    (blockCol A).transpose * blockCol A = ∑ k, (A k).transpose * A k := by
  ext i j
  simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
/-- The Gram matrix of the block row is the sum `∑_k B_k B_k^*` appearing on the
right-hand side of the manuscript's display (for real matrices the adjoint `B^*` is
the transpose). -/
theorem blockRow_mul_transpose_blockRow (B : Fin K → Matrix (Fin t) (Fin r) ℝ) :
    blockRow B * (blockRow B).transpose = ∑ k, B k * (B k).transpose := by
  ext y z
  simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
/-- For a real matrix the squared `L²` operator norm equals the operator norm of its
Gram matrix `Mᵀ M`; this is the C*-identity `‖M^* M‖ = ‖M‖²` specialized to `ℝ`,
where `star = transpose`. -/
theorem sq_opNorm_eq_opNorm_transpose_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℝ) :
    ‖M‖ ^ 2 = ‖M.transpose * M‖ := by
  rw [sq, ← Matrix.conjTranspose_eq_transpose_of_trivial M,
    Matrix.l2_opNorm_conjTranspose_mul_self]
/-- For a real matrix the squared `L²` operator norm equals the operator norm of the
Gram matrix `M Mᵀ`; this is the C*-identity `‖M M^*‖ = ‖M‖²` specialized to `ℝ`. -/
theorem sq_opNorm_eq_opNorm_mul_transpose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℝ) :
    ‖M‖ ^ 2 = ‖M * M.transpose‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self M.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
  rw [sq, ← Matrix.conjTranspose_eq_transpose_of_trivial M]
  exact h.symm
/-- **Block Cauchy--Schwarz** (Section 4, opening display of the manuscript):
for families of real blocks `A_k : Matrix (Fin r) (Fin p) ℝ` and
`B_k : Matrix (Fin t) (Fin r) ℝ`,
`‖∑_k B_k A_k‖² ≤ ‖∑_k A_k^* A_k‖ · ‖∑_k B_k B_k^*‖`,
the norm bound for the product of a block row and a block column
(for real matrices the adjoint is the transpose). -/
theorem block_cauchy_schwarz (A : Fin K → Matrix (Fin r) (Fin p) ℝ)
    (B : Fin K → Matrix (Fin t) (Fin r) ℝ) :
    ‖∑ k, B k * A k‖ ^ 2
      ≤ ‖∑ k, (A k).transpose * A k‖ * ‖∑ k, B k * (B k).transpose‖ := by
  have hsub : ‖blockRow B * blockCol A‖ ≤ ‖blockRow B‖ * ‖blockCol A‖ :=
    Matrix.l2_opNorm_mul _ _
  have hprod : ‖∑ k, B k * A k‖ ≤ ‖blockRow B‖ * ‖blockCol A‖ := by
    rwa [blockRow_mul_blockCol] at hsub
  have hnn : (0 : ℝ) ≤ ‖∑ k, B k * A k‖ := norm_nonneg _
  have hsq : ‖∑ k, B k * A k‖ ^ 2 ≤ (‖blockRow B‖ * ‖blockCol A‖) ^ 2 :=
    pow_le_pow_left₀ hnn hprod 2
  have hA : ‖blockCol A‖ ^ 2 = ‖∑ k, (A k).transpose * A k‖ := by
    rw [sq_opNorm_eq_opNorm_transpose_mul, transpose_blockCol_mul_blockCol]
  have hB : ‖blockRow B‖ ^ 2 = ‖∑ k, B k * (B k).transpose‖ := by
    rw [sq_opNorm_eq_opNorm_mul_transpose, blockRow_mul_transpose_blockRow]
  calc ‖∑ k, B k * A k‖ ^ 2
      ≤ (‖blockRow B‖ * ‖blockCol A‖) ^ 2 := hsq
    _ = ‖blockCol A‖ ^ 2 * ‖blockRow B‖ ^ 2 := by ring
    _ = ‖∑ k, (A k).transpose * A k‖ * ‖∑ k, B k * (B k).transpose‖ := by rw [hA, hB]
end
end SparseStackV3.BlockCS
