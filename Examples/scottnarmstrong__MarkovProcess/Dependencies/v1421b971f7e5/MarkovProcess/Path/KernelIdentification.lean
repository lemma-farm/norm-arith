/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Continuity.DenseTimeContinuousExtension
import Mathlib.Probability.Kernel.Composition.MapComap
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace Kernel
noncomputable section
variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]
variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
end
end Kernel
end MarkovProcess
