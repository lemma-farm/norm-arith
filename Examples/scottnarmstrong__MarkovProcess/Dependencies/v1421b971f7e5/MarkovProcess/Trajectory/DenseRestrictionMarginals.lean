/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.PhysicalReindex
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite marginals of dense restrictions of continuous trajectories

The finite-coordinate laws of the dense-time restriction of the canonical continuous trajectory
are the existing finite-set kernels, reindexed from physical time back to rational labels.  This
file makes no shift, Markov, strong Markov, or Hunt-process assertion.
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
end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
