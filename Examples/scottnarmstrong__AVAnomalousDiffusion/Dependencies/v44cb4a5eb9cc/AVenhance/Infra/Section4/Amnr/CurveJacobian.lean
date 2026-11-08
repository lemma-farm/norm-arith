-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.JacobianJetScaling
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The actual linearized Volterra operator and its primitive jets. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
instance CurveJacobian.amnrCurveEndNorm {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (C(K, E) →L[ℝ] C(K, E)) := inferInstance
instance CurveJacobian.amnrCurveEndSpace {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (C(K, E) →L[ℝ] C(K, E)) := inferInstance
instance CurveJacobian.amnrOperatorCurveNorm {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup C(K, E →L[ℝ] E) := inferInstance
instance CurveJacobian.amnrOperatorCurveSpace {K E : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ C(K, E →L[ℝ] E) := inferInstance
end AVenhance.Infra.Section4
