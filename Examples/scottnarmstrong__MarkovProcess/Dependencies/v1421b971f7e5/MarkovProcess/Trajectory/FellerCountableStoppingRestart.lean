/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.FellerRestrictedRestart
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Restart.CountableStoppingRestart
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Conditional restart of the Feller trajectory at countable-range stopping times

For a finite `NNReal`-valued stopping time with countable range, the conditional expectation of a
bounded strongly measurable functional of the canonical Feller trajectory shifted at that time,
given the stopped sigma-algebra, is the path-kernel expectation started from the state at that
time.  The proof feeds the all-time event-restricted deterministic restart identity into the
generic countable-range stopping-time bridge.

The stopping time here has countable range.  An arbitrary finite stopping time is covered in
`Trajectory/FellerStoppingConditional.lean`, and a `WithTop`-valued time that can be infinite in
`Trajectory/StoppingLtTop.lean`.
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
