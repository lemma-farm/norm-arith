/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.PrefixRecursion
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative
noncomputable section
variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
/-- Mathlib's locally finite interval and the set interval used by `DenseTimeHistory` give
measurably equivalent history spaces. -/
def denseTimeHistoryMeasurableEquiv (n : ℕ) :
    ((↑(Finset.Iic n) → α) ≃ᵐ DenseTimeHistory α n) :=
  MeasurableEquiv.piCongrLeft (fun _ : Set.Iic n ↦ α) (Equiv.IicFinsetSet n)
/-- The dense-time transition kernel on Mathlib's finite-history carrier. -/
def trajDenseStep (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (↑(Finset.Iic n) → α) α :=
  (denseStep P hP e ι n).comap (denseTimeHistoryMeasurableEquiv n)
    (denseTimeHistoryMeasurableEquiv n).measurable
/-- The transported dense-time transition kernel is Markov. -/
instance isMarkovKernel_trajDenseStep (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (trajDenseStep P hP e ι n) := by
  rw [trajDenseStep]
  let : IsMarkovKernel (denseStep P hP e ι n) :=
    isMarkovKernel_denseStep P hP e ι n
  infer_instance
/-- The time-zero history determined by an initial state. -/
def initialTrajHistory (x : α) : ↑(Finset.Iic 0) → α :=
  fun _ ↦ x
omit [StandardBorelSpace α] [Nonempty α] in
/-- The deterministic time-zero history is a measurable function of its initial state. -/
theorem measurable_initialTrajHistory : Measurable (initialTrajHistory (α := α)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_id
def dropInitialTrajCoordinate (path : ℕ → α) : ℕ → α :=
  fun n ↦ path (n + 1)
omit [StandardBorelSpace α] [Nonempty α] in
/-- Dropping the initial trajectory coordinate is measurable. -/
theorem measurable_dropInitialTrajCoordinate :
    Measurable (dropInitialTrajCoordinate (α := α)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)
/-- The countable trajectory in enumeration order, with coordinate zero corresponding to the
first observation rather than the augmented initial state. -/
def enumeratedDenseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) : Kernel α (ℕ → α) :=
  ((Kernel.traj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0).comap
      initialTrajHistory measurable_initialTrajHistory).map dropInitialTrajCoordinate
/-- The trajectory in enumeration order is a Markov kernel. -/
instance isMarkovKernel_enumeratedDenseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    IsMarkovKernel (enumeratedDenseTimeTrajectory P hP e ι) := by
  rw [enumeratedDenseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _ measurable_dropInitialTrajCoordinate
/-- Reindex the enumerated trajectory by its dense-time labels. -/
def denseTimeTrajectory (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) : Kernel α (D → α) :=
  (enumeratedDenseTimeTrajectory P hP e ι).map
    (CountableEnumeration.measurableEquivPath e α)
/-- The dense-time trajectory is a Markov kernel. -/
instance isMarkovKernel_denseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    IsMarkovKernel (denseTimeTrajectory P hP e ι) := by
  rw [denseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _
    (CountableEnumeration.measurableEquivPath e α).measurable
end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
