/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Restart.ConditionalMarkov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Stopping
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Conditional restart at countable-valued stopping times

This file upgrades deterministic-time conditional restart identities to a finite-valued or,
more generally, countable-valued finite stopping time.  It is ordinary conditional probability
infrastructure: the deterministic-time restart identity is a hypothesis here, proved for the
continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace ContinuousPath
noncomputable section
variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
end
end ContinuousPath
end MarkovProcess
