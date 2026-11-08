import Examples.balancedscorpion__shifted_square_root_fourier_classification.Dependencies.v42f27e9f8aff.MeyerProblem.Basic
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
/-- The shifted radius with one of the two possible signs. -/
def signedShiftedRadius (theta : Real) (s : RootSign) (n : Nat) : Real :=
  match s with
  | .positive => shiftedRadius theta n
  | .negative => -shiftedRadius theta n
@[simp]
theorem shiftedRadius_nonneg (theta : Real) (n : Nat) :
    0 ≤ shiftedRadius theta n :=
  Real.sqrt_nonneg _
theorem shiftedRadius_sq {theta : Real} (htheta : 0 ≤ theta) (n : Nat) :
    shiftedRadius theta n ^ 2 = (n : Real) + theta := by
  exact Real.sq_sqrt (by positivity)
@[simp]
theorem abs_signedShiftedRadius (theta : Real) (s : RootSign) (n : Nat) :
    |signedShiftedRadius theta s n| = shiftedRadius theta n := by
  cases s <;> simp [signedShiftedRadius, shiftedRadius_nonneg]
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
/-- A concrete constant used in the uniform reciprocal-polynomial separation estimate. -/
def shiftedRootSeparationConstant (theta : Real) : Real :=
  min (1 / 4) (Real.sqrt theta)
theorem shiftedRootSeparationConstant_nonneg {theta : Real} (_htheta : 0 ≤ theta) :
    0 ≤ shiftedRootSeparationConstant theta := by
  simp [shiftedRootSeparationConstant]
theorem shiftedRootSeparationConstant_le_quarter (theta : Real) :
    shiftedRootSeparationConstant theta ≤ 1 / 4 :=
  min_le_left _ _
theorem shiftedRootSeparationConstant_le_sqrt (theta : Real) :
    shiftedRootSeparationConstant theta ≤ Real.sqrt theta :=
  min_le_right _ _
theorem shiftedRootSeparationConstant_div_le_radiusGapScale
    {theta : Real} (_htheta : 0 ≤ theta) (n : Nat) :
    shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) ≤
      1 / (2 * (1 + shiftedRadius theta n)) := by
  have hdenom : 0 < 1 + shiftedRadius theta n := by
    nlinarith [shiftedRadius_nonneg theta n]
  rw [div_le_iff₀ hdenom]
  have hc := shiftedRootSeparationConstant_le_quarter theta
  field_simp
  nlinarith
theorem sqrt_theta_le_shiftedRadius {theta : Real} (_htheta : 0 ≤ theta) (n : Nat) :
    Real.sqrt theta ≤ shiftedRadius theta n := by
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (by positivity : (0 : Real) ≤ n)
theorem shiftedRootSeparationConstant_div_le_sqrt {theta : Real} (htheta : 0 ≤ theta)
    (n : Nat) :
    shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) ≤
      Real.sqrt theta := by
  have hc0 := shiftedRootSeparationConstant_nonneg htheta
  have hr0 := shiftedRadius_nonneg theta n
  have hdenom : 0 < 1 + shiftedRadius theta n := by nlinarith
  have hdiv :
      shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) ≤
        shiftedRootSeparationConstant theta := by
    rw [div_le_iff₀ hdenom]
    nlinarith
  exact hdiv.trans (shiftedRootSeparationConstant_le_sqrt theta)
/-- Distinct signed roots are separated by an explicit reciprocal-linear function of the first
root.  The asymmetry is intentional: it makes the result directly usable as an isolation radius
at the first root. -/
theorem shiftedRoot_gap_lower_bound {theta : Real} (htheta : 0 < theta)
    {s t : RootSign} {n m : Nat}
    (hne : signedShiftedRadius theta s n ≠ signedShiftedRadius theta t m) :
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
        rw [abs_signedShiftedRadius]
      _ ≤ 1 / (2 * (1 + shiftedRadius theta n)) :=
        shiftedRootSeparationConstant_div_le_radiusGapScale htheta.le n
      _ ≤ |shiftedRadius theta n - shiftedRadius theta m| :=
        shiftedRadius_abs_sub_lower htheta.le hnm
      _ = dist (signedShiftedRadius theta .positive n)
          (signedShiftedRadius theta .positive m) := by
        simp [signedShiftedRadius, Real.dist_eq]
  · calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .positive n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [abs_signedShiftedRadius]
      _ ≤ Real.sqrt theta :=
        shiftedRootSeparationConstant_div_le_sqrt htheta.le n
      _ ≤ shiftedRadius theta m := sqrt_theta_le_shiftedRadius htheta.le m
      _ ≤ dist (signedShiftedRadius theta .positive n)
          (signedShiftedRadius theta .negative m) := by
        rw [Real.dist_eq]
        simp only [signedShiftedRadius]
        rw [sub_neg_eq_add, abs_of_nonneg]
        · exact le_add_of_nonneg_left (shiftedRadius_nonneg theta n)
        · exact add_nonneg (shiftedRadius_nonneg theta n) (shiftedRadius_nonneg theta m)
  · calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .negative n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [abs_signedShiftedRadius]
      _ ≤ Real.sqrt theta :=
        shiftedRootSeparationConstant_div_le_sqrt htheta.le n
      _ ≤ shiftedRadius theta n := sqrt_theta_le_shiftedRadius htheta.le n
      _ ≤ dist (signedShiftedRadius theta .negative n)
          (signedShiftedRadius theta .positive m) := by
        rw [Real.dist_eq]
        simp only [signedShiftedRadius]
        rw [abs_of_nonpos]
        · rw [neg_sub, sub_neg_eq_add]
          exact le_add_of_nonneg_left (shiftedRadius_nonneg theta m)
        · nlinarith [shiftedRadius_nonneg theta n, shiftedRadius_nonneg theta m]
  · have hnm : n ≠ m := by
      intro h
      subst m
      exact hne rfl
    calc
      shiftedRootSeparationConstant theta /
          (1 + |signedShiftedRadius theta .negative n|) =
          shiftedRootSeparationConstant theta / (1 + shiftedRadius theta n) := by
        rw [abs_signedShiftedRadius]
      _ ≤ 1 / (2 * (1 + shiftedRadius theta n)) :=
        shiftedRootSeparationConstant_div_le_radiusGapScale htheta.le n
      _ ≤ |shiftedRadius theta n - shiftedRadius theta m| :=
        shiftedRadius_abs_sub_lower htheta.le hnm
      _ = dist (signedShiftedRadius theta .negative n)
          (signedShiftedRadius theta .negative m) := by
        rw [Real.dist_eq]
        simp only [signedShiftedRadius]
        rw [← abs_neg]
        congr 1
        ring
end
end MeyerProblem
