/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.AllTimeMarginals
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Trajectory.FiniteMarginals
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/
open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal
namespace MarkovProcess
noncomputable section
namespace ContinuousPath
end ContinuousPath
section KernelLimits
variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]
namespace SubMarkovKernelSemigroup
namespace IsConservative
variable [CompleteSpace α] [StandardBorelSpace α] [Nonempty α]
end IsConservative
end SubMarkovKernelSemigroup
end KernelLimits
end
end MarkovProcess
