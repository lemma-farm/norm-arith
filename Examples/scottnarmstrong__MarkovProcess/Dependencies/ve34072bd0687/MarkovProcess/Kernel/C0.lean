/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Examples.scottnarmstrong__MarkovProcess.Dependencies.ve34072bd0687.MarkovProcess.Kernel.Integral
import Examples.scottnarmstrong__MarkovProcess.Dependencies.ve34072bd0687.MarkovProcess.Kernel.KernelSemigroup
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Kernel operators on continuous functions vanishing at infinity

This file records the spatial `C₀` property of a sub-Markov kernel semigroup and packages its
raw integral as a contractive continuous linear map on `C₀(α, ℝ)`.  It makes no assertion about
continuity in time or the existence of an associated stochastic process.
-/
open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal ZeroAtInfty
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
/-- A kernel semigroup maps `C₀(α, ℝ)` into itself when its raw kernel integral is continuous
and vanishes at infinity at every time. -/
def MapsC0 (P : SubMarkovKernelSemigroup α) : Prop :=
  ∀ t (f : C₀(α, ℝ)),
    Continuous (kernelIntegral (P t) f) ∧
      Tendsto (kernelIntegral (P t) f) (cocompact α) (nhds 0)
variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)
variable [BorelSpace α]
end SubMarkovKernelSemigroup
end MarkovProcess
