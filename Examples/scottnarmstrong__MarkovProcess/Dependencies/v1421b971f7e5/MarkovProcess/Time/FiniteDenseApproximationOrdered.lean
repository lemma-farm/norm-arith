/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.AllTimeFiniteMarginals
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ordered form of finite dense approximations

This file expresses a finite dense-approximation kernel as a finite-time kernel at its
increasing physical times. The final coordinate reindexing is the fixed map
`orderedPathToFiniteSet I`; it does not depend on the chosen dense approximation `q`.

The construction also covers `I = ∅`. In that case the ordered time family and both path
coordinate types are empty.
-/
open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
end
end MarkovProcess.SubMarkovKernelSemigroup
