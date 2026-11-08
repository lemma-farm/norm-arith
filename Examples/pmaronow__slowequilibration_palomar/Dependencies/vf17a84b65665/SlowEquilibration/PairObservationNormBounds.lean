-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.PairObservationCrossCovariance
set_option autoImplicit false
/-! Dimension-independent norm bounds for the actual normalized pair Gram. -/
@[expose] public section
namespace SlowEquilibration.PairObservationNormBounds
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationCrossCovariance
open scoped RealInnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
def profileBound {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  1+valueProfileBound c+firstProfileBound c+secondProfileBound c+thirdProfileBound c
lemma profileBound_pos {P : ℕ} (c : Degree P → ℝ) : 0 < profileBound c := by
  unfold profileBound valueProfileBound firstProfileBound secondProfileBound thirdProfileBound
  positivity
lemma abs_triple_le {a b p L : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hp : |p| ≤ L) :
    |a*b*p| ≤ L := by
  rw [abs_mul,abs_mul]
  calc
    _ ≤ 1*1*L := by gcongr
    _ = L := by ring
lemma norm_eq_sqrt_dimension {N : ℕ} (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    ‖x‖=Real.sqrt (N:ℝ) := by
  rw [← hx,Real.sqrt_sq (norm_nonneg x)]
lemma normalized_inner_le_one {N : ℕ} (hN : 0 < N) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (V : Vector N) (hV : ‖V‖ ≤ 1) :
    |inner ℝ x V/Real.sqrt (N:ℝ)| ≤ 1 := by
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mpr
  calc
    _ ≤ ‖x‖*‖V‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (N:ℝ)*1 := by rw [norm_eq_sqrt_dimension x hx];gcongr
    _ = _ := by ring
end
end SlowEquilibration.PairObservationNormBounds
