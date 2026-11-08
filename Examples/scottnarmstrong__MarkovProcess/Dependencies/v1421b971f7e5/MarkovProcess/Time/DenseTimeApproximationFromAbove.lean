/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Continuity.DenseTimeContinuousExtension
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Dense-time approximation from above

Every nonnegative real time is the limit of a strictly decreasing sequence of dense times whose
physical values stay strictly above the limit. This includes time zero and times that already
belong to the dense carrier; choosing strict upper approximants gives one uniform API for all
cuts.

This is deterministic order-topological infrastructure and makes no stochastic-process claim.
-/
open Filter Topology
open scoped NNReal
namespace MarkovProcess
end MarkovProcess
