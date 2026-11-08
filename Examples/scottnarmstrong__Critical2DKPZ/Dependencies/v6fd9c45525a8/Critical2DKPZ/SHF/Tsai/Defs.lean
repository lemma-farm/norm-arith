/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Definitions.Plane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Mathlib
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Tsai's dense-time stochastic heat-flow axioms

The flow predicate includes
measurability, almost-sure local finiteness, approximate composition, independent
increments and the first four moment formulas. It makes no path-continuity assumption.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators CompactlySupported
namespace Critical2DKPZ.SHF.Tsai
end Critical2DKPZ.SHF.Tsai
end
