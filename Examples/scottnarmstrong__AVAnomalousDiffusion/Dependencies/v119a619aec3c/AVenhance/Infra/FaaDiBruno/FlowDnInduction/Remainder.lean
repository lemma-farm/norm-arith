-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.TransportODEApplications
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.Composition
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.ODE.Linear.Gronwall
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The lower-order Faà di Bruno term in the flow induction

This module isolates the one-block term in the ordered-finpartition chain
rule.  The remaining terms are bounded by the all-order 10421 resummation,
with the paper's coefficient and radius factors.
-/
@[expose] public section
noncomputable section
namespace AVenhance.FaaDiBruno
open FormalMultilinearSeries
open Homogenization
open MeasureTheory
open scoped ContDiff
end AVenhance.FaaDiBruno
end
