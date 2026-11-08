/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.BUC
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.HeatFlow
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.Semigroup
@[expose] public section
/-!
# The heat semigroup on bounded uniformly continuous functions

This file bundles the Gaussian heat flow as a contraction on `BUC`.  It is the functional-analytic
form of the heat evolution used in Sections 3, 5, and 6 of the cited paper.
-/
open Filter MeasureTheory ProbabilityTheory
namespace Planarwave
noncomputable section
section HeatSemigroup
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- Gaussian heat evolution, bundled as a bounded uniformly continuous function. -/
def heatFlowBUC (a t : ℝ) (f : BUC E F) : BUC E F where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup
    (heatFlow a t f)
    (continuous_heatFlow f.uniformContinuous (fun x ↦ f.norm_apply_le x))
    ‖f‖
    (fun x ↦ norm_heatFlow_le (fun y ↦ f.norm_apply_le y) x)
  uniformContinuous' :=
    uniformContinuous_heatFlow f.uniformContinuous (fun x ↦ f.norm_apply_le x)
theorem heatFlowBUC_add (a t : ℝ) (f g : BUC E F) :
    heatFlowBUC a t (f + g) = heatFlowBUC a t f + heatFlowBUC a t g := by
  ext x
  exact congrFun
    (heatFlow_add_of_bounded_continuous a t f.continuous g.continuous ‖f‖ ‖g‖
      (fun y ↦ f.norm_apply_le y) (fun y ↦ g.norm_apply_le y)) x
theorem heatFlowBUC_smul (a t r : ℝ) (f : BUC E F) :
    heatFlowBUC a t (r • f) = r • heatFlowBUC a t f := by
  ext x
  exact congrFun (heatFlow_smul a t r f) x
/-- The heat flow is a contraction in the BUC supremum norm. -/
theorem norm_heatFlowBUC_le (a t : ℝ) (f : BUC E F) : ‖heatFlowBUC a t f‖ ≤ ‖f‖ := by
  rw [BUC.norm_le (norm_nonneg f)]
  intro x
  exact norm_heatFlow_le (fun y ↦ f.norm_apply_le y) x
/-- The Gaussian heat evolution as a continuous linear contraction. -/
def heatOperator (a t : ℝ) : BUC E F →L[ℝ] BUC E F :=
  LinearMap.mkContinuous
    { toFun := heatFlowBUC a t
      map_add' := heatFlowBUC_add a t
      map_smul' := heatFlowBUC_smul a t }
    1 (fun f ↦ by simpa using norm_heatFlowBUC_le a t f)
@[simp]
theorem heatOperator_apply (a t : ℝ) (f : BUC E F) :
    heatOperator a t f = heatFlowBUC a t f := rfl
theorem norm_heatOperator_le (a t : ℝ) : ‖heatOperator (E := E) (F := F) a t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa using norm_heatFlowBUC_le a t f
theorem heatOperator_add_time {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatOperator (E := E) (F := F) a s).comp (heatOperator a t) =
      heatOperator a (s + t) := by
  ext f x
  exact congrFun
    (heatFlow_add_time ha hs ht f.uniformContinuous (fun y ↦ f.norm_apply_le y)) x
/-- The BUC-valued translated integrand whose Gaussian average is the heat flow. -/
def translatedHeatIntegrand (a t : ℝ) (f : BUC E F) (z : E) : BUC E F :=
  BUC.translate (-(heatScale a t • z)) f
theorem continuous_translatedHeatIntegrand (a t : ℝ) (f : BUC E F) :
    Continuous (translatedHeatIntegrand a t f) := by
  apply (BUC.continuous_translate f).comp
  fun_prop
theorem integrable_translatedHeatIntegrand (a t : ℝ) (f : BUC E F) :
    Integrable (translatedHeatIntegrand a t f) (stdGaussian E) := by
  refine Integrable.mono' (integrable_const ‖f‖)
    (continuous_translatedHeatIntegrand a t f).aestronglyMeasurable ?_
  filter_upwards with z
  simp [translatedHeatIntegrand]
/-- The heat flow is the Bochner integral of the translation representation used in the paper. -/
theorem heatFlowBUC_eq_integral_translate (a t : ℝ) (f : BUC E F) :
    heatFlowBUC a t f = ∫ z, translatedHeatIntegrand a t f z ∂(stdGaussian E) := by
  ext x
  change heatFlow a t f x =
    BUC.evalCLM (𝕜 := ℝ) x (∫ z, translatedHeatIntegrand a t f z ∂(stdGaussian E))
  rw [← (BUC.evalCLM (𝕜 := ℝ) x).integral_comp_comm
    (integrable_translatedHeatIntegrand a t f)]
  simp only [BUC.evalCLM_apply, translatedHeatIntegrand, BUC.translate_apply, heatFlow]
  congr 1
  funext z
  simp
theorem continuous_heatFlowBUC_time (a : ℝ) (f : BUC E F) :
    Continuous fun t ↦ heatFlowBUC a t f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  simp_rw [heatFlowBUC_eq_integral_translate]
  have hmeas : ∀ᶠ t in nhds t₀,
      AEStronglyMeasurable (translatedHeatIntegrand a t f) (stdGaussian E) := by
    filter_upwards with t
    exact (continuous_translatedHeatIntegrand a t f).aestronglyMeasurable
  have hbound : ∀ᶠ t in nhds t₀, ∀ᵐ z ∂(stdGaussian E),
      ‖translatedHeatIntegrand a t f z‖ ≤ ‖f‖ := by
    filter_upwards with t
    filter_upwards with z
    simp [translatedHeatIntegrand]
  have hlim : ∀ᵐ z ∂(stdGaussian E),
      Tendsto (fun t ↦ translatedHeatIntegrand a t f z) (nhds t₀)
        (nhds (translatedHeatIntegrand a t₀ f z)) := by
    filter_upwards with z
    have hs : Tendsto (fun t ↦ -(heatScale a t • z)) (nhds t₀)
        (nhds (-(heatScale a t₀ • z))) := by
      exact (((continuous_heatScale a).tendsto t₀).smul_const z).neg
    have hout := ((BUC.continuous_translate f).tendsto (-(heatScale a t₀ • z))).comp hs
    simpa [translatedHeatIntegrand, Function.comp_def] using hout
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : E ↦ ‖f‖)
    hmeas hbound (integrable_const ‖f‖) hlim
end HeatSemigroup
end
end Planarwave
