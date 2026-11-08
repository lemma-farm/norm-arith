/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.FellerStoppingRestart
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.StoppedValueMeasurability
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Conditional expectation of the Feller trajectory at finite stopping times

For every finite `NNReal`-valued stopping time of the canonical filtration, the conditional
expectation of a bounded strongly measurable functional of the shifted canonical Feller
trajectory, given the stopped sigma-algebra, is the path-kernel expectation started from the
state at the stopping time.  The proof feeds the event-restricted stopping-time restart identity
into the generic conditional-expectation bridge; measurability of the restarted expectation for
the stopped sigma-algebra comes from progressive measurability of the coordinate process.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
end
end MarkovProcess.SubMarkovKernelSemigroup
