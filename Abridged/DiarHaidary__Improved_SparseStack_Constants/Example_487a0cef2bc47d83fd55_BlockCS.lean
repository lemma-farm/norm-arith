import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Examples.Example_487a0cef2bc47d83fd55_BlockCS ====
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


set_option linter.unusedVariables false in
/-- **Block Cauchy--Schwarz** (Section 4, opening display of the manuscript):
for families of real blocks `A_k : Matrix (Fin r) (Fin p) ℝ` and
`B_k : Matrix (Fin t) (Fin r) ℝ`,
`‖∑_k B_k A_k‖² ≤ ‖∑_k A_k^* A_k‖ · ‖∑_k B_k B_k^*‖`,
the norm bound for the product of a block row and a block column
(for real matrices the adjoint is the transpose). -/
theorem block_cauchy_schwarz (A : Fin K → Matrix (Fin r) (Fin p) ℝ)
    (B : Fin K → Matrix (Fin t) (Fin r) ℝ) 
    (h_SparseStackV3_BlockCS_blockRow_mul_transpose_blockRow : ∀ {K r t : ℕ} (B : Fin K → Matrix (Fin t) (Fin r) ℝ),
      SparseStackV3.BlockCS.blockRow B * (SparseStackV3.BlockCS.blockRow B).transpose =
        ∑ k : Fin K, B k * (B k).transpose)
    (h_SparseStackV3_BlockCS_transpose_blockCol_mul_blockCol : ∀ {K p r : ℕ} (A : Fin K → Matrix (Fin r) (Fin p) ℝ),
      (SparseStackV3.BlockCS.blockCol A).transpose * SparseStackV3.BlockCS.blockCol A =
        ∑ k : Fin K, (A k).transpose * A k)
    (h_SparseStackV3_BlockCS_sq_opNorm_eq_opNorm_mul_transpose : ∀ {m n : Type} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq m]
      [inst_3 : DecidableEq n] (M : Matrix m n ℝ), ‖M‖ ^ 2 = ‖M * M.transpose‖)
    (h_SparseStackV3_BlockCS_sq_opNorm_eq_opNorm_transpose_mul : ∀ {m n : Type} [inst : Fintype m] [inst_1 : Fintype n] [DecidableEq m] [inst_3 : DecidableEq n]
      (M : Matrix m n ℝ), ‖M‖ ^ 2 = ‖M.transpose * M‖)
    (h_SparseStackV3_BlockCS_blockRow_mul_blockCol : ∀ {K p r t : ℕ} (A : Fin K → Matrix (Fin r) (Fin p) ℝ) (B : Fin K → Matrix (Fin t) (Fin r) ℝ),
      SparseStackV3.BlockCS.blockRow B * SparseStackV3.BlockCS.blockCol A = ∑ k : Fin K, B k * A k)
    :
    ‖∑ k, B k * A k‖ ^ 2
      ≤ ‖∑ k, (A k).transpose * A k‖ * ‖∑ k, B k * (B k).transpose‖ := by
  have hsub : ‖blockRow B * blockCol A‖ ≤ ‖blockRow B‖ * ‖blockCol A‖ :=
    Matrix.l2_opNorm_mul _ _
  have hprod : ‖∑ k, B k * A k‖ ≤ ‖blockRow B‖ * ‖blockCol A‖ := by
    rwa [h_SparseStackV3_BlockCS_blockRow_mul_blockCol] at hsub
  have hnn : (0 : ℝ) ≤ ‖∑ k, B k * A k‖ := norm_nonneg _
  have hsq : ‖∑ k, B k * A k‖ ^ 2 ≤ (‖blockRow B‖ * ‖blockCol A‖) ^ 2 :=
    pow_le_pow_left₀ hnn hprod 2
  have hA : ‖blockCol A‖ ^ 2 = ‖∑ k, (A k).transpose * A k‖ := by
    rw [h_SparseStackV3_BlockCS_sq_opNorm_eq_opNorm_transpose_mul, h_SparseStackV3_BlockCS_transpose_blockCol_mul_blockCol]
  have hB : ‖blockRow B‖ ^ 2 = ‖∑ k, B k * (B k).transpose‖ := by
    rw [h_SparseStackV3_BlockCS_sq_opNorm_eq_opNorm_mul_transpose, h_SparseStackV3_BlockCS_blockRow_mul_transpose_blockRow]
  calc ‖∑ k, B k * A k‖ ^ 2
      ≤ (‖blockRow B‖ * ‖blockCol A‖) ^ 2 := hsq
    _ = ‖blockCol A‖ ^ 2 * ‖blockRow B‖ ^ 2 := by ring
    _ = ‖∑ k, (A k).transpose * A k‖ * ‖∑ k, B k * (B k).transpose‖ := by rw [hA, hB]
end
end SparseStackV3.BlockCS
