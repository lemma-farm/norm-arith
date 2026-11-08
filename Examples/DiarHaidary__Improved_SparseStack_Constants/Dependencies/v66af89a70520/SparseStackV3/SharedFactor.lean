/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

Formalization of the operator content of the "Shared-factor Gram estimate"
(Lemma `new:shared`) of Section 3 of Version 3.0 of the manuscript
"SparseStack Is an Optimal Oblivious Subspace Embedding".
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v66af89a70520.SparseStackV3.Base.LightSectorAbstract
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v66af89a70520.SparseStackV3.Base.MatrixTail
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace SparseStackV3
namespace SharedFactor
noncomputable section
variable {M N ell d : ℕ}
theorem quadraticForm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    SparseFock.MatrixTail.quadraticForm A x =
      ∑ p, ∑ q, WithLp.ofLp x p * (A p q * WithLp.ofLp x q) := by
  rw [SparseFock.MatrixTail.quadraticForm, real_inner_comm,
    Matrix.inner_toEuclideanCLM]
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
end
end SharedFactor
end SparseStackV3
