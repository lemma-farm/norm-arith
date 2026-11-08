/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.TrajectoryMarginals
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Continuity.KolmogorovDenseTimeContinuousSupport
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Continuous-path trajectory kernels

This file transports the canonical dense-time trajectory of a conservative kernel semigroup to
continuous paths.  The explicit default is used only by the previously established measurable
extension away from the continuous-restriction range.  A coordinate Kolmogorov condition makes
that fallback irrelevant and transports the proved rational-time marginal identities.

No continuous-time Markov property, strong Markov property, Hunt-process assertion, or PDE
increment estimate is claimed.
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
/-- The canonical dense-time trajectory transported through the measurable continuous-extension
map.  Under the Kolmogorov hypothesis used below, its law is independent of `default`. -/
def continuousPathTrajectory (P : SubMarkovKernelSemigroup alpha)
    (hP : P.IsConservative) (default : ContinuousPath alpha) :
    Kernel alpha (ContinuousPath alpha) :=
  Kernel.toContinuousPathKernel
    (denseTimeTrajectory P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) default
/-- The transported continuous-path trajectory is a Markov kernel in its initial-state
parameter. -/
instance isMarkovKernel_continuousPathTrajectory
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha) :
    IsMarkovKernel (continuousPathTrajectory P hP default) := by
  unfold continuousPathTrajectory
  exact Kernel.isMarkovKernel_toContinuousPathKernel _ default
end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
