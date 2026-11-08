/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Main
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.ExitTimeShift
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The process killed at the exit time of an open set: transition kernels

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
and an open set `U`, the transition kernel at time `t` of the process **killed when it leaves
`U`** is

  `killedKernel P hP U hU t x B = Q x {ω | t < exitTime U ω ∧ ω t ∈ B}`,

the law of the position at time `t` restricted to the survival event `{t < τ_U}`.  This file
proves that these kernels are sub-Markov (`isSubMarkovKernel_killedKernel`), jointly measurable
in time and starting point (`measurable_killedKernel`), vanish off `U`
(`killedKernel_apply_of_notMem`), reduce at time zero to the identity restricted to `U`
(`killedKernel_zero`), and satisfy the Chapman--Kolmogorov law `killedKernel_add`,

  `killedKernel (s + t) = killedKernel t ∘ₖ killedKernel s`,

which follows from the Markov property of `Q` at the deterministic time `s` on the
`𝓕_s`-event `{s < τ_U}` together with the path identity `{s + t < τ} = {s < τ} ∩ {t < τ ∘ θ_s}`.

On the carrier `alpha` the family is not a `SubMarkovKernelSemigroup`, because at time zero it is
the identity only on `U` (it is `0` off `U`); the semigroup structure on the carrier `U` is a
separate packaging.  No Feller property of the killed family is claimed.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace MarkovProcess
namespace ContinuousPath
variable {alpha : Type*} [PseudoMetricSpace alpha]
variable [MeasurableSpace alpha] [BorelSpace alpha]
end ContinuousPath
namespace SubMarkovKernelSemigroup
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)
variable [LocallyCompactSpace alpha]
end SubMarkovKernelSemigroup
end MarkovProcess
