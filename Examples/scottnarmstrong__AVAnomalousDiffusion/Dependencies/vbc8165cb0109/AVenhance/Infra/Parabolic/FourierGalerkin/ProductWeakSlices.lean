-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakGradient
public import Mathlib
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Almost-every-time weak derivative slices

Separated tests identify the spatial derivative of the synchronized product limit on almost every
time slice. The first step below rewrites product-space pairings as iterated spatial pairings.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance weakSlicesMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakSlicesMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakSlicesProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakSlicesSFiniteTorus : SFinite (volume : Measure Torus) := inferInstance
local instance weakSlicesProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance weakSlicesOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
local instance weakSlicesTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance weakSlicesScalarSeparableMeasure : IsSeparable (volume : Measure Torus) :=
  inferInstance
local instance weakSlicesScalarSecondCountable : SecondCountableTopology ScalarTorusL2 :=
  inferInstance
end AVenhance.Infra.Parabolic.FourierGalerkin
end
