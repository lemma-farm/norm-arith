-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Section4.Amnr.CurveImplicit
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Flow.FlowIntegral
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The characterized flow as an actual compact-time solution curve. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
open scoped NNReal
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow
def amnrFlowCurve {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) (s a c : ℝ) (x : Vec 2) : C(Icc a c, Vec 2) :=
  ⟨fun t => X t x s,
    (continuous_iff_continuousAt.mpr (fun t => (hX.2 x s t).continuousAt)).comp continuous_subtype_val⟩
/-- Grönwall gives actual uniform continuity of the solution-curve family
with respect to its initial point, before proving any flow derivatives. -/
theorem amnrFlowCurve_lipschitz {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {L : ℝ} (hL₀ : 0 ≤ L) (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {s a c : ℝ} (hs : s ∈ Icc a c) :
    LipschitzWith (Real.exp (L * (c - a))).toNNReal (amnrFlowCurve hX s a c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro t
  change ‖X t x s - X t y s‖ ≤ _
  have ht : |(t : ℝ) - s| ≤ c - a :=
    abs_le.mpr ⟨by linarith [hs.2, t.property.1], by linarith [hs.1, t.property.2]⟩
  exact (flow_spatial_gronwall b hL hX x y s t).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hL₀)) (norm_nonneg _))
end AVenhance.Infra.Section4
