/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Time.DenseTimeHistory
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.PrefixKernel
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Conditional kernels for finite dense-time histories

This file augments finite prefix laws by their starting point and disintegrates the joint law of
a prefix and its next observation. It makes no infinite-process or path-regularity claim.
-/
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
variable {D α : Type*} [MeasurableSpace α]
def nextObservationJoint (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α ((Fin n → α) × α) :=
  Kernel.mapOfMeasurable (denseTimePrefixKernel P e ι (n + 1))
    (DenseTimeHistory.splitLast n) (DenseTimeHistory.splitLast n).measurable
namespace IsConservative
variable [StandardBorelSpace α] [Nonempty α]
def observationCondKernel (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (α × (Fin n → α)) α := by
  letI : IsMarkovKernel (nextObservationJoint P e ι n) := by
    rw [nextObservationJoint, Kernel.mapOfMeasurable_eq_map]
    let : IsMarkovKernel (denseTimePrefixKernel P e ι (n + 1)) :=
      hP.isMarkovKernel_denseTimePrefixKernel P e ι (n + 1)
    exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.splitLast n).measurable
  exact (nextObservationJoint P e ι n).condKernel
/-- The conditional next-observation law is Markov. -/
theorem isMarkovKernel_observationCondKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (observationCondKernel P hP e ι n) := by
  rw [observationCondKernel]
  infer_instance
def denseStep (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (DenseTimeHistory α n) α :=
  Kernel.comap (observationCondKernel P hP e ι n)
    (DenseTimeHistory.historyEquiv n) (DenseTimeHistory.historyEquiv n).measurable
/-- The finite-history next-observation kernel is Markov. -/
theorem isMarkovKernel_denseStep (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (denseStep P hP e ι n) := by
  rw [denseStep]
  let : IsMarkovKernel (observationCondKernel P hP e ι n) :=
    isMarkovKernel_observationCondKernel P hP e ι n
  infer_instance
end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess
