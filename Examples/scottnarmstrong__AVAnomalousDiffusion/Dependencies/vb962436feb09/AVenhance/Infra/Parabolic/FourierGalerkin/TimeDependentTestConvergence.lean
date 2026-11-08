-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentWeakEquation
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Spacetime convergence of the smooth-test Fourier cutoffs

The spatial Fourier tails from `Section5.TestDensity` are integrated in time by dominated
convergence. These estimates are the strong `L²` convergence needed to pass the product weak
equation from finite cutoffs to a general smooth spacetime test.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance timeTestConvergenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance timeTestConvergenceMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance timeTestConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance timeTestConvergenceProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
end AVenhance.Infra.Parabolic.FourierGalerkin
end
