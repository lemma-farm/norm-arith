/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.DelayedHeatForcing
@[expose] public section
/-!
# The fixed smoothing factor in the delayed forcing

Because every nonzero pulse has age greater than `1/4`, a heat factor of age
`1/8` can always be moved onto its source. This is the precise interface
between the delayed forcing and the derivative-free estimate of Lemma 4.2.
-/
open MeasureTheory Set
namespace Planarwave
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- Strong heat continuity plus its uniform contraction bound gives joint continuity. -/
theorem continuous_heatFlowBUC_joint (a : ℝ) :
    Continuous (fun p : ℝ × BUC E F ↦ heatFlowBUC a p.1 p.2) := by
  have h : ContinuousOn (fun p : ℝ × BUC E F ↦ heatFlowBUC a p.1 p.2) (univ ×ˢ univ) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ 1
    · intro t _
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (K := 1) (norm_heatOperator_le (E := E) (F := F) a t)).lipschitzOnWith
    · intro f _
      exact (continuous_heatFlowBUC_time a f).continuousOn
  simpa only [univ_prod_univ, continuousOn_univ] using h
theorem heatFlowBUC_add_apply {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : BUC E F) : heatFlowBUC a (s + t) f = heatFlowBUC a s (heatFlowBUC a t f) := by
  exact (congrArg (fun L : BUC E F →L[ℝ] BUC E F ↦ L f) (heatOperator_add_time ha hs ht)).symm
theorem intervalIntegrable_delayedHeatBlock (a : ℝ) (N : ℝ → BUC E F) (n : ℕ)
    (hN : ContinuousOn N (Icc (n : ℝ) ((n : ℝ) + 1))) :
    IntervalIntegrable (fun r ↦ heatFlowBUC a ((n : ℝ) + 1 - r) (N r)) volume
      (n : ℝ) ((n : ℝ) + 1) :=
  ((continuous_heatFlowBUC_joint a).comp_continuousOn
    ((continuousOn_const.sub continuousOn_id).prodMk hN)).intervalIntegrable_of_Icc (by linarith)
end
end Planarwave
