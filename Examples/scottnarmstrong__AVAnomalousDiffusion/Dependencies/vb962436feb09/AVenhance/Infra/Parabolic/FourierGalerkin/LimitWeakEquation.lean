-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentTestAdmissibility
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentCutoffProduct
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Physical weak equation for smooth Fourier cutoffs

The synchronized product-space identity is transferred to the Euclidean cell using the
physical time-torus measure-preserving map and the selected scalar and gradient representatives.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance limitWeakEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance limitWeakEquationMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance limitWeakEquationProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance limitWeakEquationProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance limitWeakEquationProbabilityTime : IsProbabilityMeasure GalerkinTimeMeasure := by
  refine ⟨?_⟩
  simp [GalerkinTimeMeasure, Real.volume_Ioc]
end AVenhance.Infra.Parabolic.FourierGalerkin
end
