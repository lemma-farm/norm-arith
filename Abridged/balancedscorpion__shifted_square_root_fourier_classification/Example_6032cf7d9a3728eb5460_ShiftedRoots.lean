import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.Notation

-- ==== Examples.balancedscorpion__shifted_square_root_fourier_classification.Examples.Example_6032cf7d9a3728eb5460_ShiftedRoots ====
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
/-- The gap to any other radius, measured from the radius at `n`, has the same reciprocal-linear
lower bound. -/
theorem shiftedRadius_abs_sub_lower {theta : Real} (htheta : 0 ≤ theta)
    {n m : Nat} (hnm : n ≠ m) 
    (h_MeyerProblem_shiftedRadius_strictMono : ∀ {theta : ℝ}, 0 ≤ theta → StrictMono (MeyerProblem.shiftedRadius theta))
    (h_MeyerProblem_shiftedRadius_nonneg : ∀ (theta : ℝ) (n : ℕ), 0 ≤ MeyerProblem.shiftedRadius theta n)
    (h_MeyerProblem_shiftedRadius_forward_gap_lower : ∀ {theta : ℝ},
      0 ≤ theta →
        ∀ {n m : ℕ},
          n < m →
            1 / (2 * (1 + MeyerProblem.shiftedRadius theta n)) ≤
              MeyerProblem.shiftedRadius theta m - MeyerProblem.shiftedRadius theta n)
    :
    1 / (2 * (1 + shiftedRadius theta n)) ≤
      |shiftedRadius theta n - shiftedRadius theta m| := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hmono : shiftedRadius theta n ≤ shiftedRadius theta m :=
      (h_MeyerProblem_shiftedRadius_strictMono htheta).monotone hlt.le
    rw [abs_of_nonpos (sub_nonpos.2 hmono)]
    simpa only [neg_sub] using h_MeyerProblem_shiftedRadius_forward_gap_lower htheta hlt
  · have hmono : shiftedRadius theta m ≤ shiftedRadius theta n :=
      (h_MeyerProblem_shiftedRadius_strictMono htheta).monotone hgt.le
    rw [abs_of_nonneg (sub_nonneg.2 hmono)]
    have hdenom :
        2 * (1 + shiftedRadius theta m) ≤ 2 * (1 + shiftedRadius theta n) := by
      nlinarith
    have hrecip :
        1 / (2 * (1 + shiftedRadius theta n)) ≤
          1 / (2 * (1 + shiftedRadius theta m)) := by
      apply one_div_le_one_div_of_le
      · nlinarith [h_MeyerProblem_shiftedRadius_nonneg theta m]
      · exact hdenom
    exact hrecip.trans (h_MeyerProblem_shiftedRadius_forward_gap_lower htheta hgt)
end
end MeyerProblem
