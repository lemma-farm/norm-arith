-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.v13616b19efac.SlowEquilibration.SphericalConcentration
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
set_option autoImplicit false
@[expose] public section
/-! Ordinary integral partition functions for bounded measurable families of
linear fields. The spin measure may be nonatomic, including the genuine
uniform sphere law. Differentiation is proved by dominated convergence. -/
namespace SlowEquilibration.GaussianSpinInterpolation
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
variable {V H : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
def weight (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) (v : V) : ℝ :=
  ρ v * Real.exp (L v w)
def moment (ν : Measure V) (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) : ℝ :=
  ∫ v, weight ρ L w v ∂ν
theorem weight_measurable (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) (w : H) : Measurable (weight ρ L w) :=
  hρ.mul (((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp)
theorem weight_bound (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    {C K : ℝ} {v : V} (hρ : |ρ v| ≤ C) (hL : ‖L v‖ ≤ K) (w : H) :
    ‖weight ρ L w v‖ ≤ C * Real.exp (K * ‖w‖) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hρ
  have hexp : Real.exp (L v w) ≤ Real.exp (K * ‖w‖) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans ((L v).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))))
  rw [weight, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul hρ hexp (Real.exp_pos _).le hC
theorem weight_integrable (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    Integrable (weight ρ L w) ν :=
  Integrable.of_bound (weight_measurable ρ L hρ hL w).aestronglyMeasurable _
    (hb.mono (fun _ hv => weight_bound ρ L hv.1 hv.2 w))
def expectation (ν : Measure V) (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) : ℝ :=
  moment ν ρ L w / moment ν (fun _ => 1) L w
theorem moment_one_pos (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    0 < moment ν (fun _ => 1) L w := by
  have hi := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun v hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  change Integrable (fun v => 1 * Real.exp (L v w)) ν at hi
  simpa only [moment, weight, one_mul] using integral_exp_pos
    (by simpa only [one_mul] using hi)
theorem norm_moment_le (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    ‖moment ν ρ L w‖ ≤ C * moment ν (fun _ => 1) L w := by
  have hi := weight_integrable ν ρ L hρ hL hb w
  have h1 := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun v hv => ⟨by norm_num, hv.2⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  calc
    _ ≤ ∫ v, ‖weight ρ L w v‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ v, C * weight (fun _ => 1) L w v ∂ν := by
      apply integral_mono_ae hi.norm (h1.const_mul C)
      filter_upwards [hb] with v hv
      simp only [weight, norm_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
      exact mul_le_mul_of_nonneg_right hv.1 (Real.exp_pos _).le
    _ = _ := integral_const_mul C _
theorem norm_expectation_le (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    ‖expectation ν ρ L w‖ ≤ C := by
  have hz := moment_one_pos ν L hL (hb.mono (fun _ hv => hv.2)) w
  rw [expectation, norm_div, Real.norm_of_nonneg hz.le]
  exact (div_le_iff₀ hz).mpr (norm_moment_le ν ρ L hρ hL hC hb w)
def gibbsMeasure (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) : Measure V :=
  ν.withDensity (fun v => ENNReal.ofReal
    (Real.exp (L v w) / moment ν (fun _ => 1) L w))
theorem gibbsMeasure_absolutelyContinuous (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) :
    gibbsMeasure ν L w ≪ ν := withDensity_absolutelyContinuous _ _
theorem gibbsMeasure_probability (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) : IsProbabilityMeasure (gibbsMeasure ν L w) := by
  have hz := moment_one_pos ν L hL hb w
  have hi := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  change Integrable (fun v => 1*Real.exp (L v w)) ν at hi
  simp only [one_mul] at hi
  constructor
  rw [gibbsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (.of_forall fun v => (div_pos (Real.exp_pos _) hz).le), integral_div]
  have hm : (∫ v, Real.exp (L v w) ∂ν) = moment ν (fun _ => 1) L w := by
    simp only [moment, weight, one_mul]
  rw [hm, div_self hz.ne', ENNReal.ofReal_one]
theorem integral_gibbsMeasure (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) (ρ : V → ℝ) :
    (∫ v, ρ v ∂gibbsMeasure ν L w) = expectation ν ρ L w := by
  have hz := moment_one_pos ν L hL hb w
  have hm : Measurable (fun v => Real.exp (L v w) / moment ν (fun _ => 1) L w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp.div_const _
  rw [gibbsMeasure, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (div_pos (Real.exp_pos _) hz).le, smul_eq_mul]
  unfold expectation moment
  rw [← integral_div]
  apply integral_congr_ae
  exact .of_forall fun v => by simp only [weight]; ring
end
end SlowEquilibration.GaussianSpinInterpolation
