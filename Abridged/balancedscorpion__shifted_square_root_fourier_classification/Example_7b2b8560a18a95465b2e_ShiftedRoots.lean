import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.Notation

-- ==== Examples.balancedscorpion__shifted_square_root_fourier_classification.Examples.Example_7b2b8560a18a95465b2e_ShiftedRoots ====
/-!
# Shifted square-root geometry

This file formalises the signed support points

`+-sqrt (n + theta)`, for `n : Nat`.

The hypothesis `0 < theta` is used precisely where the positive and negative branches must be
disjoint.  Statements that only need the square-root arguments to be nonnegative use the weaker
hypothesis `0 <= theta`.
-/
namespace MeyerProblem
noncomputable section
open Metric Set

namespace RootSign
end RootSign
/-- `sqrt (n + theta)`, with `n` coerced to the reals. -/
def shiftedRadius (theta : Real) (n : Nat) : Real :=
  Real.sqrt ((n : Real) + theta)


set_option linter.unusedVariables false in
/-- The gap to the next radius has an explicit reciprocal-linear lower bound. -/
theorem shiftedRadius_succ_gap_lower {theta : Real} (htheta : 0 ≤ theta) (n : Nat) 
    (h_MeyerProblem_shiftedRadius_succ_sub : ∀ {theta : ℝ},
      0 ≤ theta →
        ∀ (n : ℕ),
          MeyerProblem.shiftedRadius theta (n + 1) - MeyerProblem.shiftedRadius theta n =
            1 / (MeyerProblem.shiftedRadius theta (n + 1) + MeyerProblem.shiftedRadius theta n))
    (h_MeyerProblem_shiftedRadius_nonneg : ∀ (theta : ℝ) (n : ℕ), 0 ≤ MeyerProblem.shiftedRadius theta n)
    (h_MeyerProblem_shiftedRadius_succ_le_add_one : ∀ {theta : ℝ},
      0 ≤ theta →
        ∀ (n : ℕ), MeyerProblem.shiftedRadius theta (n + 1) ≤ MeyerProblem.shiftedRadius theta n + 1)
    :
    1 / (2 * (1 + shiftedRadius theta n)) ≤
      shiftedRadius theta (n + 1) - shiftedRadius theta n := by
  rw [h_MeyerProblem_shiftedRadius_succ_sub htheta]
  apply one_div_le_one_div_of_le
  · have hpos : 0 < shiftedRadius theta (n + 1) := by
      apply Real.sqrt_pos.2
      positivity
    exact add_pos_of_pos_of_nonneg hpos (h_MeyerProblem_shiftedRadius_nonneg theta n)
  · have hle := h_MeyerProblem_shiftedRadius_succ_le_add_one htheta n
    nlinarith [h_MeyerProblem_shiftedRadius_nonneg theta n]
end
end MeyerProblem
