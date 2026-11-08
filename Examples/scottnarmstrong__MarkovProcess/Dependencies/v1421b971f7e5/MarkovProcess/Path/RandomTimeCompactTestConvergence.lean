/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.ShiftCompactTestConvergence
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Kernel.PositiveC0OperatorMeasure
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.RandomShiftMeasurability
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Dominated convergence for tests along random times

This file records path-side dominated-convergence tools for a sequence of measurable random
times converging pointwise to a limiting random time.  The measure is any finite measure on
continuous-path space; no Markov or kernel assumption is used.  The deterministic-sequence
versions are in `ContinuousPathShiftCompactTestConvergence.lean`.
-/
open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported
namespace MarkovProcess
noncomputable section
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
end
end MarkovProcess
