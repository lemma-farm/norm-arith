import Examples.balancedscorpion__shifted_square_root_fourier_classification.Dependencies.v31784bc8d5d8.MeyerProblem.Basic
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
instance : Fintype RootSign where
  elems := {.positive, .negative}
  complete s := by cases s <;> simp
namespace RootSign
end RootSign
/-- `sqrt (n + theta)`, with `n` coerced to the reals. -/
def shiftedRadius (theta : Real) (n : Nat) : Real :=
  Real.sqrt ((n : Real) + theta)
@[simp]
theorem shiftedRadius_nonneg (theta : Real) (n : Nat) :
    0 ≤ shiftedRadius theta n :=
  Real.sqrt_nonneg _
theorem shiftedRadius_sq {theta : Real} (htheta : 0 ≤ theta) (n : Nat) :
    shiftedRadius theta n ^ 2 = (n : Real) + theta := by
  exact Real.sq_sqrt (by positivity)
theorem shiftedRadius_succ_sub {theta : Real} (htheta : 0 ≤ theta) (n : Nat) :
    shiftedRadius theta (n + 1) - shiftedRadius theta n =
      1 / (shiftedRadius theta (n + 1) + shiftedRadius theta n) := by
  have hpos : 0 < shiftedRadius theta (n + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have hdenom : shiftedRadius theta (n + 1) + shiftedRadius theta n ≠ 0 := by
    exact (add_pos_of_pos_of_nonneg hpos (shiftedRadius_nonneg theta n)).ne'
  apply (eq_div_iff hdenom).2
  calc
    (shiftedRadius theta (n + 1) - shiftedRadius theta n) *
        (shiftedRadius theta (n + 1) + shiftedRadius theta n) =
        shiftedRadius theta (n + 1) ^ 2 - shiftedRadius theta n ^ 2 := by ring
    _ = ((n + 1 : Nat) : Real) + theta - ((n : Real) + theta) := by
      rw [shiftedRadius_sq htheta, shiftedRadius_sq htheta]
    _ = 1 := by norm_num
theorem shiftedRadius_succ_le_add_one {theta : Real} (htheta : 0 ≤ theta) (n : Nat) :
    shiftedRadius theta (n + 1) ≤ shiftedRadius theta n + 1 := by
  have hn := shiftedRadius_nonneg theta n
  have hsucc := shiftedRadius_nonneg theta (n + 1)
  have hn_sq := shiftedRadius_sq htheta n
  have hsucc_sq := shiftedRadius_sq htheta (n + 1)
  norm_num at hsucc_sq
  nlinarith
/-- The gap to the next radius has an explicit reciprocal-linear lower bound. -/
theorem shiftedRadius_succ_gap_lower {theta : Real} (htheta : 0 ≤ theta) (n : Nat) :
    1 / (2 * (1 + shiftedRadius theta n)) ≤
      shiftedRadius theta (n + 1) - shiftedRadius theta n := by
  rw [shiftedRadius_succ_sub htheta]
  apply one_div_le_one_div_of_le
  · have hpos : 0 < shiftedRadius theta (n + 1) := by
      apply Real.sqrt_pos.2
      positivity
    exact add_pos_of_pos_of_nonneg hpos (shiftedRadius_nonneg theta n)
  · have hle := shiftedRadius_succ_le_add_one htheta n
    nlinarith [shiftedRadius_nonneg theta n]
end
end MeyerProblem
