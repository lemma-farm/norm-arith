-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Ambient.Euclidean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.Ball
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Mollify.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit false
set_option warningAsError true
/-!
# A smooth ball cut-off with two derivative bounds

The native carrier is `Fin 3 → ℝ`.  The cut-off below is obtained by
convolving the indicator of the `7ρ/10` ball with a normalized smooth bump.
The bump is chosen with a slightly smaller inherited-metric radius so that
its Euclidean support has a strict collar in the native carrier.  This keeps
the stated Euclidean radii literal while avoiding an implicit change of norm.
-/
open Set MeasureTheory Metric
open scoped Convolution
set_option autoImplicit false
noncomputable section
namespace CKN
private lemma vecEuclideanNorm_eq_l2 (x : Vec 3) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring
private lemma vecEuclideanNorm_add_le (x y : Vec 3) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [vecEuclideanNorm_eq_l2, vecEuclideanNorm_eq_l2, vecEuclideanNorm_eq_l2]
  rw [WithLp.toLp_add]
  exact norm_add_le _ _
private lemma vecEuclideanNorm_eq_spaceEuclideanNorm (x : Vec 3) :
    vecEuclideanNorm x = spaceEuclideanNorm x := by
  simp [vecEuclideanNorm, spaceEuclideanNorm, vecNormSq, vecDot, pow_two]
private lemma euclideanBall_measurable (x₀ : Vec 3) (R : ℝ) :
    MeasurableSet (euclideanBall x₀ R) := by
  change MeasurableSet ((fun x : Vec 3 => euclideanSqDist x x₀) ⁻¹' Iio (R ^ 2))
  exact measurableSet_Iio.preimage
    (contDiff_euclideanSqDist_left x₀).continuous.measurable
private def ballIndicator (x₀ : Vec 3) (R : ℝ) : Vec 3 → ℝ :=
  (euclideanBall x₀ R).indicator (fun _ => 1)
private lemma ballIndicator_locallyIntegrable (x₀ : Vec 3) (R : ℝ) :
    LocallyIntegrable (ballIndicator x₀ R) volume := by
  exact (locallyIntegrable_const (1 : ℝ)).indicator
    (euclideanBall_measurable x₀ R)
private def unitBallCutoff : Vec 3 → ℝ :=
  mollify (ballIndicator 0 (7 / 10)) (1 / 100) (by norm_num)
private lemma unitBallCutoff_smooth :
    ContDiff ℝ (⊤ : ℕ∞) unitBallCutoff := by
  simpa [unitBallCutoff] using
    (mollify_contDiff (d := 3) (u := ballIndicator 0 (7 / 10))
      (ε := (1 / 100 : ℝ)) (by norm_num)
      (ballIndicator_locallyIntegrable 0 (7 / 10)))
private lemma mollifier_mem_ball_of_ne_zero {ε : ℝ} (hε : 0 < ε)
    {y : Vec 3} (hy : mollifier ε hε y ≠ 0) :
    y ∈ Metric.ball 0 ε := by
  have hy' : y ∈ Function.support (mollifier ε hε) := hy
  have hy'' : y ∈ Metric.ball (0 : Vec 3) ε := by
    change y ∈ Function.support ((standardMollifier (d := 3) ε hε).normed volume) at hy'
    rw [(standardMollifier (d := 3) ε hε).support_normed_eq] at hy'
    simpa [standardMollifier] using hy'
  simpa [Metric.mem_ball, dist_eq_norm] using hy''
private lemma unitBallCutoff_eq_zero_of_not_mem_closedBall {x : Vec 3}
    (hx : x ∉ euclideanClosedBall 0 (73 / 100)) : unitBallCutoff x = 0 := by
  rw [unitBallCutoff, mollify, MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : mollifier (1 / 100 : ℝ) (by norm_num) y = 0
  · rw [hy]
    simp
  · have hyball := mollifier_mem_ball_of_ne_zero (by norm_num : (0 : ℝ) < 1 / 100) hy
    have hynorm : ‖y‖ < (1 / 100 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hyball
    by_cases hbase : ballIndicator 0 (7 / 10) (x - y) = 0
    · simp [hbase]
    · have hxy : x - y ∈ euclideanBall 0 (7 / 10) := by
        by_contra hnot
        apply hbase
        simp [ballIndicator, hnot]
      have hxy' : vecEuclideanNorm (x - y) < (7 / 10 : ℝ) := by
        simpa using (mem_euclideanBall_iff_vecEuclideanNorm_lt
          (x₀ := (0 : Vec 3)) (x := x - y) (by norm_num)).mp hxy
      have hye : vecEuclideanNorm y < (3 / 100 : ℝ) := by
        calc
          vecEuclideanNorm y ≤ 3 * ‖y‖ := by
            simpa [vecEuclideanNorm_eq_spaceEuclideanNorm] using
              (euclideanNorm_le_three_mul_space_norm y)
          _ < 3 / 100 := by nlinarith only [hynorm]
      have hsum := vecEuclideanNorm_add_le (x - y) y
      have heq : x - 0 = (x - y) + y := by abel
      have hlt : vecEuclideanNorm (x - 0) < (73 / 100 : ℝ) := by
        rw [heq]
        linarith only [hsum, hxy', hye]
      exact False.elim (hx ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num : (0 : ℝ) ≤ 73 / 100)).2 hlt.le))
private lemma unitBallCutoff_tsupport_subset :
    tsupport unitBallCutoff ⊆ euclideanClosedBall 0 (73 / 100) := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (unitBallCutoff_eq_zero_of_not_mem_closedBall hnot)
  · exact isClosed_euclideanClosedBall 0 (73 / 100)
/-- The convolution cut-off at center `x₀` and radius `ρ`. -/
def mollifiedBallCutoff (x₀ : Vec 3) {ρ : ℝ} (_hρ : 0 < ρ) : Vec 3 → ℝ :=
  fun x => unitBallCutoff (ρ⁻¹ • (x - x₀))
theorem mollifiedBallCutoff_smooth (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff x₀ hρ) := by
  unfold mollifiedBallCutoff
  apply unitBallCutoff_smooth.comp
  fun_prop
private lemma unitGradient_eq_zero_of_not_mem_closedBall {x : Vec 3}
    (hx : x ∉ euclideanClosedBall 0 (73 / 100)) :
    classicalGradient unitBallCutoff x = 0 := by
  have hx' : x ∉ tsupport unitBallCutoff := by
    intro h
    exact hx (unitBallCutoff_tsupport_subset h)
  have hfd : fderiv ℝ unitBallCutoff x = 0 :=
    fderiv_of_notMem_tsupport ℝ hx'
  funext i
  rw [classicalGradient_apply, hfd]
  simp
private lemma unitGradient_hasCompactSupport :
    HasCompactSupport (classicalGradient unitBallCutoff) := by
  refine HasCompactSupport.intro
    (isCompact_euclideanClosedBall (d := 3) 0 (R := (73 / 100 : ℝ))
      (by norm_num)) ?_
  intro x hx
  exact unitGradient_eq_zero_of_not_mem_closedBall hx
private lemma unitGradient_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (classicalGradient unitBallCutoff) := by
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => (fderiv ℝ unitBallCutoff x) (basisVec i))
  have hfd := unitBallCutoff_smooth.contDiff_fderiv_apply
    (m := (⊤ : ℕ∞)) (by simp)
  let hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 3 => (x, basisVec i)) :=
    contDiff_id.prodMk (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 3 => basisVec i))
  have hcomp := hfd.comp hmap
  simpa [Function.comp_def] using hcomp
private lemma unitGradient_norm_continuous :
    Continuous (fun x => vecEuclideanNorm (classicalGradient unitBallCutoff x)) := by
  have hgrad : Continuous (classicalGradient unitBallCutoff) :=
    unitGradient_smooth.continuous
  unfold vecEuclideanNorm vecNormSq vecDot
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _hi
  exact ((continuous_apply i).comp hgrad).mul ((continuous_apply i).comp hgrad)
private lemma unitHessian_norm_continuous :
    Continuous (fun x => ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖) := by
  exact (unitGradient_smooth.continuous_fderiv (by simp)).norm
private lemma unitHessian_hasCompactSupport :
    HasCompactSupport (fderiv ℝ (classicalGradient unitBallCutoff)) := by
  exact unitGradient_hasCompactSupport.fderiv ℝ
/-- The absolute unit-scale gradient constant of the convolution cut-off. -/
noncomputable def cutoffGradientConstant : ℝ :=
  sSup (Set.range (fun x : Vec 3 =>
    vecEuclideanNorm (classicalGradient unitBallCutoff x)))
/-- The absolute unit-scale second-derivative constant of the convolution
cut-off. -/
noncomputable def cutoffSecondDerivativeConstant : ℝ :=
  sSup (Set.range (fun x : Vec 3 =>
    ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖))
private lemma cutoffGradientConstant_bddAbove :
    BddAbove (Set.range (fun x : Vec 3 =>
      vecEuclideanNorm (classicalGradient unitBallCutoff x))) := by
  exact unitGradient_norm_continuous.bddAbove_range_of_hasCompactSupport
    (HasCompactSupport.intro
      (isCompact_euclideanClosedBall (d := 3) 0 (R := (73 / 100 : ℝ))
        (by norm_num)) (by
        intro x hx
        rw [unitGradient_eq_zero_of_not_mem_closedBall hx]
        simp [vecEuclideanNorm, vecNormSq, vecDot]))
private lemma cutoffSecondDerivativeConstant_bddAbove :
    BddAbove (Set.range (fun x : Vec 3 =>
      ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖)) := by
  exact unitHessian_norm_continuous.bddAbove_range_of_hasCompactSupport
    unitHessian_hasCompactSupport.norm
private lemma unitGradient_norm_le_constant (x : Vec 3) :
    vecEuclideanNorm (classicalGradient unitBallCutoff x) ≤
      cutoffGradientConstant := by
  exact le_csSup cutoffGradientConstant_bddAbove (Set.mem_range_self x)
private lemma unitHessian_norm_le_constant (x : Vec 3) :
    ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖ ≤
      cutoffSecondDerivativeConstant := by
  exact le_csSup cutoffSecondDerivativeConstant_bddAbove (Set.mem_range_self x)
private lemma mollifiedBallCutoff_gradient_formula (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    classicalGradient (mollifiedBallCutoff x₀ hρ) x =
      ρ⁻¹ • classicalGradient unitBallCutoff (ρ⁻¹ • (x - x₀)) := by
  have hA : HasFDerivAt (fun y : Vec 3 => ρ⁻¹ • (y - x₀))
      (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)) x := by
    have hid := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
    simpa using hid.const_smul (ρ⁻¹ : ℝ)
  have hunit : DifferentiableAt ℝ unitBallCutoff
      (ρ⁻¹ • (x - x₀)) :=
    unitBallCutoff_smooth.differentiable (by simp) _
  have hcomp := hunit.hasFDerivAt.comp x hA
  funext i
  change (fderiv ℝ
      (fun y : Vec 3 => unitBallCutoff (ρ⁻¹ • (y - x₀))) x) (basisVec i) = _
  rw [show (fun y : Vec 3 => unitBallCutoff (ρ⁻¹ • (y - x₀))) =
      unitBallCutoff ∘ (fun y : Vec 3 => ρ⁻¹ • (y - x₀)) by rfl]
  rw [hcomp.fderiv]
  simp [classicalGradient, smul_eq_mul]
private lemma mollifiedBallCutoff_hessian_formula (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x =
      ρ⁻¹ • ((fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))).comp
        (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3))) := by
  have hA : HasFDerivAt (fun y : Vec 3 => ρ⁻¹ • (y - x₀))
      (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)) x := by
    have hid := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
    simpa using hid.const_smul (ρ⁻¹ : ℝ)
  have hgrad : DifferentiableAt ℝ (classicalGradient unitBallCutoff)
      (ρ⁻¹ • (x - x₀)) :=
    unitGradient_smooth.differentiable (by simp) _
  have hcomp := hgrad.hasFDerivAt.comp x hA
  have hscaled := hcomp.const_smul (ρ⁻¹ : ℝ)
  have hfun : classicalGradient (mollifiedBallCutoff x₀ hρ) =
      (fun y : Vec 3 => ρ⁻¹ • classicalGradient unitBallCutoff
        (ρ⁻¹ • (y - x₀))) := by
    funext y
    exact mollifiedBallCutoff_gradient_formula x₀ hρ y
  rw [hfun]
  have hpointwise :
      (ρ⁻¹ • (classicalGradient unitBallCutoff ∘
        (fun y : Vec 3 => ρ⁻¹ • (y - x₀)))) =
      (fun y : Vec 3 => ρ⁻¹ • classicalGradient unitBallCutoff
        (ρ⁻¹ • (y - x₀))) := by
    funext y
    rfl
  rw [← hpointwise]
  simpa [Function.comp_def] using hscaled.fderiv
theorem mollifiedBallCutoff_gradient_bound (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) x) ≤
      cutoffGradientConstant / ρ := by
  rw [mollifiedBallCutoff_gradient_formula]
  rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)]
  calc
    ρ⁻¹ * vecEuclideanNorm
        (classicalGradient unitBallCutoff (ρ⁻¹ • (x - x₀))) ≤
        ρ⁻¹ * cutoffGradientConstant :=
      mul_le_mul_of_nonneg_left (unitGradient_norm_le_constant _) (by positivity)
    _ = cutoffGradientConstant / ρ := by
      field_simp [hρ.ne']
theorem mollifiedBallCutoff_second_derivative_bound (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    ‖fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x‖ ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  rw [mollifiedBallCutoff_hessian_formula]
  calc
    ‖ρ⁻¹ • ((fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))).comp
        (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)))‖ =
        ‖ρ⁻¹‖ * ‖(fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))).comp
        (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3))‖ := norm_smul _ _
    _ ≤ ρ⁻¹ * (‖fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))‖ *
        ‖ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)‖) := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = (ρ⁻¹) ^ 2 * ‖fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ),
        ContinuousLinearMap.norm_id]
      ring
    _ ≤ (ρ⁻¹) ^ 2 * cutoffSecondDerivativeConstant := by
      exact mul_le_mul_of_nonneg_left (unitHessian_norm_le_constant _)
        (by positivity)
    _ = cutoffSecondDerivativeConstant / ρ ^ 2 := by
      field_simp [hρ.ne']
end CKN
