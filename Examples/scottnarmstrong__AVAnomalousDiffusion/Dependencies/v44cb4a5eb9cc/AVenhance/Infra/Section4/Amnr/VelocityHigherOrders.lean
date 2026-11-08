-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.CurveJetOperators
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Auxiliary finite-order stream-regularity bounds, without restricting the paper budget.
The stream-regularity estimates control every spatial order. Auxiliary constants may use a larger finite
order while each paper derivative retains its separately checked budget. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow
end AVenhance.Infra.Section4
