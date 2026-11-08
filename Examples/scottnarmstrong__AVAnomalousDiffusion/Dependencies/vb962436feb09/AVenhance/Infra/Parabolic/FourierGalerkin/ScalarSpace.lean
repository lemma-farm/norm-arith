-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.ProjectionCoefficients
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scalar spatial `L²` synthesis for the real Fourier frame

The orthonormal scalar Fourier modes synthesize an isometric copy of the finite coefficient
space inside scalar torus `L²`. This is the common state space for the cutoff paths and the
coefficient energy estimate.
-/
@[expose] public section
noncomputable section
open MeasureTheory
local instance scalarSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Scalar-valued spatial `L²` on the unit torus. -/
abbrev ScalarTorusL2 := Lp ℝ 2 (volume : Measure Torus)
end AVenhance.Infra.Parabolic.FourierGalerkin
end
