-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.ProductCompactness
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Torus.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Product-space realization of the drift

The drift is measurable on the Euclidean space-time cell. This module transfers that
measurability to time times the quotient torus, where the product-space Galerkin limits live.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance frozenProductMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenProductMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenProductProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance frozenProductProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance frozenProductSFiniteTorus : SFinite (volume : Measure Torus) := inferInstance
local instance frozenProductTopHolderTwo : (⊤ : ENNReal).HolderTriple 2 2 :=
  ENNReal.HolderTriple.symm
local instance frozenProductTopHolderTop : (⊤ : ENNReal).HolderTriple ⊤ ⊤ :=
  ENNReal.HolderTriple.symm
end AVenhance.Infra.Parabolic.FourierGalerkin
end
