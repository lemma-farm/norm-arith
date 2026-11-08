/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Restart.RationalRestart
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Restart.RationalRestrictedRestart
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Restart.ConditionalMarkov
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Rational-time conditional Markov identities for the continuous trajectory

This file derives two local consequences of the rational joint restart law for the canonical
continuous-path trajectory.  First, restricting to any event in the canonical filtration and
then shifting at a rational time gives the path kernel restarted from the state at that time.
Second, every bounded strongly measurable functional of the shifted path satisfies the
corresponding conditional-expectation formula.

The times here are rational.  The strong Markov property at an arbitrary finite stopping time
is in `Trajectory/FellerStoppingRestart.lean`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
