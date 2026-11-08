/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.BUC
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
@[expose] public section
namespace BUC
noncomputable section
variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]
/-- Compactly supported continuous tests belong to the BUC space. -/
def ofCompactSupport (f : X → F) (hf : Continuous f) (hc : HasCompactSupport f) : BUC X F :=
  { toBCF :=
      { toFun := f
        continuous_toFun := hf
        map_bounded' := by
          obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
          exact ⟨2 * C, fun x y ↦ (dist_le_norm_add_norm _ _).trans
            (by linarith [hC ⟨x, rfl⟩, hC ⟨y, rfl⟩])⟩ }
    uniformContinuous' := hc.uniformContinuous_of_continuous hf }
variable [MeasurableSpace X] [BorelSpace X] [NormedSpace ℝ F]
end
end BUC
