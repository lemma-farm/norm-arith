import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.Notation

-- ==== Examples.balancedscorpion__shifted_square_root_fourier_classification.Examples.Example_5d57637c17f41ed8bbe8_ShiftedRoots ====
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
/-- The two branches of the shifted square-root support. -/
inductive RootSign where
  | positive
  | negative
  deriving DecidableEq, Repr

namespace RootSign
end RootSign
/-- `sqrt (n + theta)`, with `n` coerced to the reals. -/
def shiftedRadius (theta : Real) (n : Nat) : Real :=
  Real.sqrt ((n : Real) + theta)
/-- The shifted radius with one of the two possible signs. -/
def signedShiftedRadius (theta : Real) (s : RootSign) (n : Nat) : Real :=
  match s with
  | .positive => shiftedRadius theta n
  | .negative => -shiftedRadius theta n

/-- A concrete constant used in the uniform reciprocal-polynomial separation estimate. -/
def shiftedRootSeparationConstant (theta : Real) : Real :=
  min (1 / 4) (Real.sqrt theta)


set_option linter.unusedVariables false in
/-- Distinct signed roots are separated by an explicit reciprocal-linear function of the first
root.  The asymmetry is intentional: it makes the result directly usable as an isolation radius
at the first root. -/
theorem shiftedRoot_gap_lower_bound {theta : Real} (htheta : 0 < theta)
    {s t : RootSign} {n m : Nat}
    (hne : signedShiftedRadius theta s n ≠ signedShiftedRadius theta t m) 
    (h_MeyerProblem_sqrt_theta_le_shiftedRadius : ∀ {theta : ℝ}, 0 ≤ theta → ∀ (n : ℕ), √theta ≤ MeyerProblem.shiftedRadius theta n)
    (h_MeyerProblem_shiftedRadius_abs_sub_lower : ∀ {theta : ℝ},
      0 ≤ theta →
        ∀ {n m : ℕ},
          n ≠ m →
            1 / (2 * (1 + MeyerProblem.shiftedRadius theta n)) ≤
              |MeyerProblem.shiftedRadius theta n - MeyerProblem.shiftedRadius theta m|)
    (h_MeyerProblem_abs_signedShiftedRadius : ∀ (theta : ℝ) (s : MeyerProblem.RootSign) (n : ℕ),
      |MeyerProblem.signedShiftedRadius theta s n| = MeyerProblem.shiftedRadius theta n)
    (h_MeyerProblem_shiftedRootSeparationConstant_div_le_sqrt : ∀ {theta : ℝ},
      0 ≤ theta →
        ∀ (n : ℕ),
          MeyerProblem.shiftedRootSeparationConstant theta / (1 + MeyerProblem.shiftedRadius theta n) ≤
            √theta)
    (h_MeyerProblem_shiftedRootSeparationConstant_div_le_radiusGapScale : ∀ {theta : ℝ},
      0 ≤ theta →
        ∀ (n : ℕ),
          MeyerProblem.shiftedRootSeparationConstant theta / (1 + MeyerProblem.shiftedRadius theta n) ≤
            1 / (2 * (1 + MeyerProblem.shiftedRadius theta n)))
    (h_MeyerProblem_shiftedRadius_nonneg : ∀ (theta : ℝ) (n : ℕ), 0 ≤ MeyerProblem.shiftedRadius theta n)
    :
    shiftedRootSeparationConstant theta /
        (1 + |signedShiftedRadius theta s n|) ≤
      dist (signedShiftedRadius theta s n) (signedShiftedRadius theta t m) := by
  cases s <;> cases t
  · have hnm : n ≠ m := by
      intro h
      subst m
      exact hne rfl
    calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .positive n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [h_MeyerProblem_abs_signedShiftedRadius]
      _ ≤ 1 / (2 * (1 + shiftedRadius theta n)) :=
        h_MeyerProblem_shiftedRootSeparationConstant_div_le_radiusGapScale htheta.le n
      _ ≤ |shiftedRadius theta n - shiftedRadius theta m| :=
        h_MeyerProblem_shiftedRadius_abs_sub_lower htheta.le hnm
      _ = dist (signedShiftedRadius theta .positive n)
          (signedShiftedRadius theta .positive m) := by
        simp [signedShiftedRadius, Real.dist_eq]
  · calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .positive n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [h_MeyerProblem_abs_signedShiftedRadius]
      _ ≤ Real.sqrt theta :=
        h_MeyerProblem_shiftedRootSeparationConstant_div_le_sqrt htheta.le n
      _ ≤ shiftedRadius theta m := h_MeyerProblem_sqrt_theta_le_shiftedRadius htheta.le m
      _ ≤ dist (signedShiftedRadius theta .positive n)
          (signedShiftedRadius theta .negative m) := by
        rw [Real.dist_eq]
        simp only [signedShiftedRadius]
        rw [sub_neg_eq_add, abs_of_nonneg]
        · exact le_add_of_nonneg_left (h_MeyerProblem_shiftedRadius_nonneg theta n)
        · exact add_nonneg (h_MeyerProblem_shiftedRadius_nonneg theta n) (h_MeyerProblem_shiftedRadius_nonneg theta m)
  · calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .negative n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [h_MeyerProblem_abs_signedShiftedRadius]
      _ ≤ Real.sqrt theta :=
        h_MeyerProblem_shiftedRootSeparationConstant_div_le_sqrt htheta.le n
      _ ≤ shiftedRadius theta n := h_MeyerProblem_sqrt_theta_le_shiftedRadius htheta.le n
      _ ≤ dist (signedShiftedRadius theta .negative n)
          (signedShiftedRadius theta .positive m) := by
        rw [Real.dist_eq]
        simp only [signedShiftedRadius]
        rw [abs_of_nonpos]
        · rw [neg_sub, sub_neg_eq_add]
          exact le_add_of_nonneg_left (h_MeyerProblem_shiftedRadius_nonneg theta m)
        · nlinarith [h_MeyerProblem_shiftedRadius_nonneg theta n, h_MeyerProblem_shiftedRadius_nonneg theta m]
  · have hnm : n ≠ m := by
      intro h
      subst m
      exact hne rfl
    calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .negative n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [h_MeyerProblem_abs_signedShiftedRadius]
      _ ≤ 1 / (2 * (1 + shiftedRadius theta n)) :=
        h_MeyerProblem_shiftedRootSeparationConstant_div_le_radiusGapScale htheta.le n
      _ ≤ |shiftedRadius theta n - shiftedRadius theta m| :=
        h_MeyerProblem_shiftedRadius_abs_sub_lower htheta.le hnm
      _ = dist (signedShiftedRadius theta .negative n)
          (signedShiftedRadius theta .negative m) := by
        rw [Real.dist_eq]
        simp only [signedShiftedRadius]
        rw [← abs_neg]
        congr 1
        ring
end
end MeyerProblem
