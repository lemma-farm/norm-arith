-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Section4.Amnr.VelocitySpatialLipschitz
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Quantitative actual third spatial flow operators. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow
instance FlowThirdVariationRates.amnrBilinearNorm :
    NormedAddCommGroup (Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2) := inferInstance
instance FlowThirdVariationRates.amnrBilinearSpace :
    NormedSpace ℝ (Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2) := inferInstance
end AVenhance.Infra.Section4
