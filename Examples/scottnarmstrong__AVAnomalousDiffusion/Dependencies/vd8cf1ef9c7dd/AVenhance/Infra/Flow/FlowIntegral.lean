-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8cf1ef9c7dd.AVenhance.Statements.Flow.IsFlow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8cf1ef9c7dd.AVenhance.Infra.Flow.PeriodicSmooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Integral formulation of a characterized flow trajectory. -/
@[expose] public section
open Homogenization
open MeasureTheory
open scoped ContDiff Topology
namespace AVenhance.Infra.Flow
end AVenhance.Infra.Flow
