import Examples.balancedscorpion__shifted_square_root_fourier_classification.Dependencies.v8cefa5d48ea7.MeyerProblem.Basic
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
theorem shiftedRadius_strictMono {theta : Real} (htheta : 0 ≤ theta) :
    StrictMono (shiftedRadius theta) := by
  intro m n hmn
  apply Real.sqrt_lt_sqrt
  · positivity
  · have hmn' : (m : Real) < (n : Real) := by exact_mod_cast hmn
    simpa [add_comm] using add_lt_add_right hmn' theta
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
/-- Any later radius is at least the explicit next-neighbour gap away. -/
theorem shiftedRadius_forward_gap_lower {theta : Real} (htheta : 0 ≤ theta)
    {n m : Nat} (hnm : n < m) :
    1 / (2 * (1 + shiftedRadius theta n)) ≤
      shiftedRadius theta m - shiftedRadius theta n := by
  have hsucc_le : shiftedRadius theta (n + 1) ≤ shiftedRadius theta m := by
    apply (shiftedRadius_strictMono htheta).monotone
    omega
  exact (shiftedRadius_succ_gap_lower htheta n).trans (sub_le_sub_right hsucc_le _)
/-- The gap to any other radius, measured from the radius at `n`, has the same reciprocal-linear
lower bound. -/
theorem shiftedRadius_abs_sub_lower {theta : Real} (htheta : 0 ≤ theta)
    {n m : Nat} (hnm : n ≠ m) :
    1 / (2 * (1 + shiftedRadius theta n)) ≤
      |shiftedRadius theta n - shiftedRadius theta m| := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hmono : shiftedRadius theta n ≤ shiftedRadius theta m :=
      (shiftedRadius_strictMono htheta).monotone hlt.le
    rw [abs_of_nonpos (sub_nonpos.2 hmono)]
    simpa only [neg_sub] using shiftedRadius_forward_gap_lower htheta hlt
  · have hmono : shiftedRadius theta m ≤ shiftedRadius theta n :=
      (shiftedRadius_strictMono htheta).monotone hgt.le
    rw [abs_of_nonneg (sub_nonneg.2 hmono)]
    have hdenom :
        2 * (1 + shiftedRadius theta m) ≤ 2 * (1 + shiftedRadius theta n) := by
      nlinarith
    have hrecip :
        1 / (2 * (1 + shiftedRadius theta n)) ≤
          1 / (2 * (1 + shiftedRadius theta m)) := by
      apply one_div_le_one_div_of_le
      · nlinarith [shiftedRadius_nonneg theta m]
      · exact hdenom
    exact hrecip.trans (shiftedRadius_forward_gap_lower htheta hgt)
end
end MeyerProblem
