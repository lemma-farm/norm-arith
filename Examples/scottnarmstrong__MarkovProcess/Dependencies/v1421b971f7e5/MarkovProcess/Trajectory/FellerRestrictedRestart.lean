/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.DenseRestrictionMarginals
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.RationalConditional
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Time.DenseTimeApproximationFromAbove
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.ShiftCompactTestConvergence
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Feller.DensePhysicalFiniteSetContinuity
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.MeasureIdentification
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Event-restricted deterministic restart for the Feller trajectory

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the deterministic-time canonical filtration. The proof approaches the
time strictly from above by dense times, identifies every finite dense future marginal by compact
tests, and then uses measure identification on dense restrictions.

The time here is deterministic. The strong Markov property at a finite stopping time is in
`Trajectory/FellerStoppingRestart.lean`.
-/
open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
end
end MarkovProcess.SubMarkovKernelSemigroup
