-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Section4.HMinusOneNorm
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Ergodic.HMinusOne
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Ergodic.HMinusOneErgodicCore
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Tools for the extended-valued homogeneous negative norm. The
mean-zero bridge retains the distinction between all periodic tests and the
centred tests used in Ergodic. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5
local instance avInfraSection5HMinusToolsIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]
end AVenhance.Infra.Section5
