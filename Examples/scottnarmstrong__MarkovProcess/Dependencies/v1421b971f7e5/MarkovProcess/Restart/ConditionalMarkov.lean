/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.Shift
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Deterministic-time conditional restart on continuous paths

This file specializes the generic conditional-expectation bridge to canonical continuous-path
space.  The required input is the full future restart identity after restriction to every event in
the canonical filtration at the restart time.  An unconditional shifted-law identity is only the
special case of the input for the whole path space and does not imply the result below.

The theorem is a conditional API: it does not prove its restricted restart-law hypothesis and does
not by itself associate a Markov or Hunt process with a transition semigroup.
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
