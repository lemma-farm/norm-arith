-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarFourierDerivative
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Section5.TestDensity
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth periodic spatial tests from the real Fourier identities

The synchronized limit has a common full-measure set of times on which its weak spatial
derivative identity holds for every real Fourier mode. This module begins the density bridge from
those modes to the smooth periodic tests used by the solution predicate.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Ergodic
open scoped RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance testDensityBridgeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance testDensityBridgeMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance testDensityBridgeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance testDensityBridgeProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance avInfraParabolicFourierGalerkinTestDensityBridgeIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]
end AVenhance.Infra.Parabolic.FourierGalerkin
end
