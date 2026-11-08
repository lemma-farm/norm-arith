module
public import Examples.masakioshikawa__rp2_rp3_lean.Dependencies.vdc4796f0da7a.RP2.Model
public import Mathlib
public section
/-!
Adapted from OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, licensed under Apache-2.0.
Copyright OpenAI. The namespace and imports have been changed and the
interaction-independent lemmas separated from the O(n) Gibbs model.
-/
namespace RP2.Rotation
universe uR uS uΩ uF
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
abbrev Spin (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
abbrev SpinOperator (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
@[expose] instance spinOperator_completeSpace (dimension : ℕ) : CompleteSpace (SpinOperator dimension) :=
  ContinuousLinearMap.instCompleteSpace
@[expose] instance spinOperator_ratNormedAlgebra (n : ℕ) : NormedAlgebra ℚ (SpinOperator n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _
open scoped Matrix
@[expose] def matrixOperator {n : ℕ} : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] SpinOperator n :=
  (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℝ (Fin n))).trans
    (Module.End.toContinuousLinearMap (EuclideanSpace ℝ (Fin n)))
theorem matrixOperator_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    matrixOperator M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := by
  change (Matrix.toLin (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n)) M) v = _
  rw [← Matrix.toLpLin_eq_toLin, Matrix.toLpLin_apply]
@[expose] def axisMatrixA : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,0; 0,0,-1; 0,1,0]
@[expose] def axisMatrixB : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,1; 0,0,0; -1,0,0]
@[expose] def axisA : SpinOperator 3 := matrixOperator axisMatrixA
@[expose] def axisB : SpinOperator 3 := matrixOperator axisMatrixB
theorem axisA_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisA v = WithLp.toLp 2 ![0, -v 2, v 1] := by
  rw [axisA, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
theorem axisA_norm_le : ‖axisA‖ ≤ 1 := by
  apply axisA.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisA_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 0‖]
theorem axisB_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisB v = WithLp.toLp 2 ![v 2, 0, -v 0] := by
  rw [axisB, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
theorem axisB_norm_le : ‖axisB‖ ≤ 1 := by
  apply axisB.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisB_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 1‖]
@[expose] def mixedMatrixAABB : Matrix (Fin 3) (Fin 3) ℝ := (-1/6 : ℝ) • (axisMatrixA^2+axisMatrixB^2)
@[expose] def mixedAABB : SpinOperator 3 := matrixOperator mixedMatrixAABB
end
end RP2.Rotation
