-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.SpacetimeCompactness
public import Mathlib
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Product-space weak compactness for the explicit Galerkin sums

This file realizes the finite real Fourier paths as functions on time times the torus. Their
product-space `L²` bounds are the same scalar and dissipation bounds used for the Bochner paths.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance productCompactnessMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance productCompactnessMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance productCompactnessProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance productCompactnessTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance productCompactnessOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
local instance productCompactnessTopHolderTwo : (⊤ : ENNReal).HolderTriple 2 2 := by
  exact ENNReal.HolderTriple.symm
/-- The physical time measure used in the product-space realization. -/
abbrev GalerkinTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
/-- Scalar product-space `L²` on `(0,1) × 𝕋²`. -/
abbrev ScalarProductTimeL2 := Lp ℝ 2 (GalerkinTimeMeasure.prod (volume : Measure Torus))
/-- Vector-gradient product-space `L²` on `(0,1) × 𝕋²`. -/
abbrev GradientProductTimeL2 :=
  Lp SpatialVector 2 (GalerkinTimeMeasure.prod (volume : Measure Torus))
local instance productCompactnessTimeSeparable : IsSeparable GalerkinTimeMeasure := inferInstance
local instance productCompactnessTorusSeparable :
    IsSeparable (volume : Measure Torus) := inferInstance
local instance productCompactnessProductMeasureSeparable :
    IsSeparable (GalerkinTimeMeasure.prod (volume : Measure Torus)) := inferInstance
local instance productCompactnessScalarSecondCountable :
    SecondCountableTopology ScalarProductTimeL2 := inferInstance
local instance productCompactnessGradientSecondCountable :
    SecondCountableTopology GradientProductTimeL2 := inferInstance
local instance productCompactnessScalarSeparable :
    TopologicalSpace.SeparableSpace ScalarProductTimeL2 := inferInstance
local instance productCompactnessGradientSeparable :
    TopologicalSpace.SeparableSpace GradientProductTimeL2 := inferInstance
end AVenhance.Infra.Parabolic.FourierGalerkin
end
