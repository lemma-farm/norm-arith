/- Copyright (c) 2026 Diar Heidary. Released under the MIT license. -/
import SparseStackV3.ConcreteSharedFactor.Sum
import Mathlib
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SparseStackV3.ConcreteSharedFactor

noncomputable section

variable {ρ η : Type*} [Fintype ρ] [Fintype η] [DecidableEq ρ] [DecidableEq η]

def spectator (A : Matrix η η ℝ) : Matrix (ρ × η) (ρ × η) ℝ :=
  fun x y => if x.1 = y.1 then A x.2 y.2 else 0

def fiber (z : EuclideanSpace ℝ (ρ × η)) (r : ρ) : EuclideanSpace ℝ η :=
  WithLp.toLp 2 (fun i => WithLp.ofLp z (r,i))

theorem spectator_hermitian (A : Matrix η η ℝ) (hA : A.IsHermitian) :
    (spectator (ρ := ρ) A).IsHermitian := by
  have ha : A.transpose = A := by
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  change (spectator A).conjTranspose = spectator A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext x y
  have h := congrArg (fun M : Matrix η η ℝ => M x.2 y.2) ha
  simpa [spectator,Matrix.transpose_apply,eq_comm] using
    congrArg (fun t : ℝ => if x.1=y.1 then t else 0) h

theorem quadratic_spectator (A : Matrix η η ℝ) (z : EuclideanSpace ℝ (ρ × η)) :
    SparseFock.MatrixTail.quadraticForm (spectator A) z =
      ∑ r, SparseFock.MatrixTail.quadraticForm A (fiber z r) := by
  simp only [SharedFactor.quadraticForm_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  simp [spectator,fiber]

theorem sum_fiber_norm_sq (z : EuclideanSpace ℝ (ρ × η)) :
    (∑ r, ‖fiber z r‖^2) = ‖z‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  rfl

theorem spectator_norm_le (A : Matrix η η ℝ) (hA : A.IsHermitian) :
    ‖spectator (ρ := ρ) A‖ ≤ ‖A‖ := by
  rw [SparseFock.MatrixTail.opNorm_le_iff_quadraticForm _
    (spectator_hermitian A hA) _ (norm_nonneg _)]
  intro z
  rw [quadratic_spectator]
  calc
    |∑ r, SparseFock.MatrixTail.quadraticForm A (fiber z r)| ≤
        ∑ r, |SparseFock.MatrixTail.quadraticForm A (fiber z r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ‖A‖ * ‖fiber z r‖^2 := by
      apply Finset.sum_le_sum
      intro r _
      exact (SparseFock.MatrixTail.opNorm_le_iff_quadraticForm A hA ‖A‖
        (norm_nonneg A)).mp le_rfl (fiber z r)
    _ = ‖A‖ * ‖z‖^2 := by rw [← Finset.mul_sum,sum_fiber_norm_sq]

end

end SparseStackV3.ConcreteSharedFactor
