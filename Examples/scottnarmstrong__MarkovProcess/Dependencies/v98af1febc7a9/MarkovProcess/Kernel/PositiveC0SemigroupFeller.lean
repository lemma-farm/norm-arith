/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Feller.Semigroup
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.PositiveC0SemigroupKernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Feller property of kernels represented by positive `C₀` semigroups

The kernel semigroup represented by a strongly continuous semigroup of positive contractions
recovers the original operators on `C₀` and therefore satisfies the existing Feller interface.
This file makes no conservativity, stochastic-process, or Hunt-process claim.
-/
open Filter MeasureTheory ProbabilityTheory Topology
open scoped ZeroAtInfty
namespace MarkovProcess.PositiveC0SemigroupFeller
open MarkovProcess.Semigroup
variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
variable (S : StronglyContinuousContractionSemigroup C₀(α, ℝ))
  (hS : ∀ t, PositiveC0OperatorMeasure.IsPositive (S t))
end MarkovProcess.PositiveC0SemigroupFeller
