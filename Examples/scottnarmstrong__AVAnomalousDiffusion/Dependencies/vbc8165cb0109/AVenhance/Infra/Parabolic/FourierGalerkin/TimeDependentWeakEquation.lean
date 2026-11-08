-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakLimitPassage
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Weak equation for time-dependent finite Fourier tests

The separated Fourier-mode identities sum to the weak equation for the spatial Fourier cutoff of
an arbitrary smooth periodic spacetime test.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance timeWeakEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance timeWeakEquationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance timeWeakEquationProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance timeWeakEquationProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
end AVenhance.Infra.Parabolic.FourierGalerkin
end
