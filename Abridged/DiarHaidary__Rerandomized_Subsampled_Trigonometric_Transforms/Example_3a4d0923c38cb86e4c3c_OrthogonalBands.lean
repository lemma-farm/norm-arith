import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Kronecker

-- ==== Examples.DiarHaidary__Rerandomized_Subsampled_Trigonometric_Transforms.Examples.Example_3a4d0923c38cb86e4c3c_OrthogonalBands ====
namespace SRHT.OrthogonalBands
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
variable {B I J : Type*} [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]


set_option linter.unusedVariables false in
theorem norm_sum_sq_le (A : B → Matrix I J ℝ)
    (h : ∀ b c, b≠c → (A b).transpose*A c=0) 
    (h_SRHT_OrthogonalBands_gram_sum : ∀ {B : Type u_1} {I : Type u_2} {J : Type u_3} [inst : Fintype B] [DecidableEq B]
      [inst_2 : Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (A : B → Matrix I J ℝ),
      (∀ (b c : B), b ≠ c → (A b).transpose * A c = 0) →
        (∑ b : B, A b).transpose * ∑ b : B, A b = ∑ b : B, (A b).transpose * A b)
    :
    ‖∑ b, A b‖^2 ≤ ∑ b, ‖A b‖^2 := by
  have he (M : Matrix I J ℝ) : ‖M.transpose*M‖=‖M‖^2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self M
  rw [← he,h_SRHT_OrthogonalBands_gram_sum A h]
  calc
    _ ≤ ∑ b, ‖(A b).transpose*A b‖ := norm_sum_le _ _
    _ = _ := by simp_rw [he]

end
end SRHT.OrthogonalBands
