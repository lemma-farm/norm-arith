-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.v13616b19efac.SlowEquilibration.GaussianSpinInterpolation
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
set_option autoImplicit false
@[expose] public section
namespace SlowEquilibration.GaussianSpinComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {ι V : Type*} [Fintype ι] [MeasurableSpace V]
/-- The actual diagonal linear map on the Euclidean disorder coordinates. -/
def diagonal (a : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => a i • PiLp.proj 2 (fun _ : ι => ℝ) i))
omit [Fintype ι] in
@[simp] theorem diagonal_apply (a : ι → ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    diagonal a w i = a i * w i := rfl
theorem diagonal_norm_le (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (w : EuclideanSpace ℝ ι) : ‖diagonal a w‖ ≤ C*‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg w))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonal_apply, mul_pow]
  have hsq : (a i)^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hC).mpr (ha i)
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
def coordinateMask (label : ι → Bool) (b : Bool) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  diagonal (fun i => if label i = b then 1 else 0)
def rotation (label : ι → Bool) (θ : ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Real.cos θ • coordinateMask label true + Real.sin θ • coordinateMask label false
def rotationCoefficient (label : ι → Bool) (θ : ℝ) (i : ι) : ℝ :=
  if label i then Real.cos θ else Real.sin θ
@[simp] theorem rotation_apply (label : ι → Bool) (θ : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    rotation label θ w i = rotationCoefficient label θ i * w i := by
  cases h : label i <;>
    simp [rotation, coordinateMask, PiLp.add_apply, PiLp.smul_apply, rotationCoefficient, h]
theorem rotation_norm_le (label : ι → Bool) (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖rotation label θ w‖ ≤ ‖w‖ := by
  have heq : rotation label θ = diagonal (rotationCoefficient label θ) := by
    ext g i
    simp only [rotation_apply, diagonal_apply]
  rw [heq]
  simpa only [one_mul] using diagonal_norm_le (rotationCoefficient label θ) zero_le_one
    (fun i => by cases h : label i <;> simp only [rotationCoefficient, h]
                 <;> first | exact Real.abs_cos_le_one θ | exact Real.abs_sin_le_one θ) w
def rotatedLinear (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Bool) (θ : ℝ) :=
  fun v => (L v).comp (rotation label θ)
theorem rotatedLinear_measurable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (label : ι → Bool) (θ : ℝ) : Measurable (rotatedLinear L label θ) := by
  have hc : Continuous (fun l : EuclideanSpace ℝ ι →L[ℝ] ℝ => l.comp (rotation label θ)) :=
    continuous_id.clm_comp continuous_const
  exact hc.measurable.comp hL
theorem rotatedLinear_bound (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (θ : ℝ) :
    ∀ᵐ v ∂ν, ‖rotatedLinear L label θ v‖ ≤ K := by
  filter_upwards [hb] with v hv
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro w
  exact ((L v).le_opNorm (rotation label θ w)).trans
    ((mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg _)))
variable [DecidableEq ι]
def coordinateObservable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (i : ι) : V → ℝ :=
  fun v => L v (EuclideanSpace.single i 1)
theorem coordinateObservable_measurable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (i : ι) : Measurable (coordinateObservable L i) :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hL
theorem coordinateObservable_bound (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (i : ι) : ∀ᵐ v ∂ν, |coordinateObservable L i v| ≤ K := by
  filter_upwards [hb] with v hv
  have hh := (L v).le_opNorm (EuclideanSpace.single i 1)
  have he : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ ι)‖ = 1 := by simp
  rw [Real.norm_eq_abs, he, mul_one] at hh
  exact hh.trans hv
def covarianceSign (label : ι → Bool) (i : ι) : ℝ := if label i then -1 else 1
def signedKernel (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Bool) (v u : V) : ℝ :=
  ∑ i, covarianceSign label i * (coordinateObservable L i v * coordinateObservable L i u)
theorem gibbsCoordinate_memLp (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (θ : ℝ)
    (w : EuclideanSpace ℝ ι) (i : ι) :
    MemLp (coordinateObservable L i) 2 (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
  have : IsProbabilityMeasure (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) :=
    GaussianSpinInterpolation.gibbsMeasure_probability ν _ (rotatedLinear_measurable L hL label θ)
      (rotatedLinear_bound ν L hK hb label θ) w
  apply MemLp.of_bound (coordinateObservable_measurable L hL i).aestronglyMeasurable K
  exact ((coordinateObservable_bound ν L hb i).mono (fun v hv => by
    simpa only [Real.norm_eq_abs] using hv)).filter_mono
    (GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w).ae_le
end
end SlowEquilibration.GaussianSpinComparison
