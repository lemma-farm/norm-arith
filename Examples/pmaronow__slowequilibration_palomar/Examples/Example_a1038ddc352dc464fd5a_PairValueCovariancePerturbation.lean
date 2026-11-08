-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.PairValueObservationGrouping
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.PairScoreCovariancePerturbation
set_option autoImplicit false
/-! Proper scalar-value conditional covariance, including pure mixtures.
No inverse of the singular pure value/radial score covariance is taken. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedObservationCoercivity
open PairObservationCrossCovariance PairObservationNormBounds SphericalTwoPointCovariance
open ScalarCoefficientCovariance SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
lemma normalizedValue_dual {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) (u : ℝ) :
    (innerSL ℝ u).comp (normalizedValue c x)=(u/Real.sqrt (N:ℝ)) • valueCLM c x := by
  ext g
  simp only [normalizedValue,ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,
    RCLike.inner_apply,conj_trivial,smul_eq_mul]
  ring
lemma value_gradient_cross_inner {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (f : Fin m → Vector N)
    (u : ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ u (normalizedValue c x ((gradientCLM c y f).adjoint v))=
      u*firstCovariance c (overlap x y)*(inner ℝ x (frameSum f v)/Real.sqrt (N:ℝ)) := by
  rw [← scalarCross_dual,normalizedValue_dual,gradientCLM_dual,scalarCross_smul_left]
  change (u/Real.sqrt (N:ℝ))*scalarCross
    (flatJetCLM c 0 x (fun i => Fin.elim0 i)) (flatJetCLM c 1 y (fun _ => frameSum f v))=_
  rw [scalarCross_flatJet,covariance_comm,gradient_value_covariance hN c hc y x,overlap_comm,real_inner_comm]
  ring
lemma value_gradient_cross_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ‖(normalizedValue c x).comp (gradientCLM c y f).adjoint‖ ≤ profileBound c*|overlap x y|^(d-1) := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (normalizedValue c x ((gradientCLM c y f).adjoint v)) u ≤ _
  rw [real_inner_comm,value_gradient_cross_inner hN c hc]
  have huc : |u| ≤ 1 := by simpa only [Real.norm_eq_abs] using hu.le
  have hV : ‖frameSum f v‖ ≤ 1 := by rw [frameSum_norm f hf,hv]
  have hi:=normalized_inner_le_one hN x hx (frameSum f v) hV
  have hp:=(profile_order_common c d hdeg hr).2.1
  exact (le_abs_self _).trans (by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le huc hi hp)
end
end SlowEquilibration.NormalizedPairObservations
