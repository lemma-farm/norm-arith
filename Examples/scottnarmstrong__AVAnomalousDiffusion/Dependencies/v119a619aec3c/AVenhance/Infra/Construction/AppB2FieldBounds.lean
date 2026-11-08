-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.RecursionIncrement
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.TransportODEApplications
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The Section 2 induction bound controls all positive spatial seminorms of
the stream velocity. -/
@[expose] public section
open Homogenization MeasureTheory
open scoped ContDiff
noncomputable section
namespace AVenhance.Infra.Construction
open AVenhance.FaaDiBruno
end AVenhance.Infra.Construction
end
