-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.IsPeriodicH1With
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Linear operations on periodic weak gradients

Cell `L²` control and periodicity imply global integrability against compact tests. This lets the
whole-space weak derivative identities be subtracted without relying on junk integral values.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
namespace AVenhance.Infra.Parabolic.WeakUniqueness
theorem WeakAlgebra.weak_unitCube_volume_lt_top : volume AVenhance.unitCube < ⊤ := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]
local instance weak_finite_unitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ] using WeakAlgebra.weak_unitCube_volume_lt_top
theorem WeakAlgebra.weakTimeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]
local instance weak_finite_timeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [WeakAlgebra.weakTimeCube_measure_eq_product]
  infer_instance
end AVenhance.Infra.Parabolic.WeakUniqueness
end
