/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.ConditionalKernel
import Mathlib.Probability.Kernel.Composition.Lemmas
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# One-step recursion for finite dense-time histories

This file identifies the result of adjoining one conditionally sampled observation to an
augmented finite history. It makes no infinite-process or path-regularity claim.
-/
open MeasureTheory ProbabilityTheory
namespace ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
namespace MarkovProcess
namespace DenseTimeHistory
variable {α : Type*} [MeasurableSpace α]
end DenseTimeHistory
namespace SubMarkovKernelSemigroup
noncomputable section
variable {D α : Type*} [MeasurableSpace α]
namespace IsConservative
variable [StandardBorelSpace α] [Nonempty α]
end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess
