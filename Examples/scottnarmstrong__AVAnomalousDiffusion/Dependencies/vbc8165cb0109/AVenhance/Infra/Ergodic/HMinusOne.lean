-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Ergodic.AveragesL2
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Ergodic.Flow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Torus.FourierCalculus
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The homogeneous negative Sobolev duality on the unit torus -/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory
open scoped ENNReal
noncomputable section
def HMinusOne.closedUnitCube (d : ℕ) : Set (Homogenization.Vec d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1
theorem HMinusOne.unitCell_subset_closedUnitCube (d : ℕ) :
    Torus.unitCell d ⊆ HMinusOne.closedUnitCube d := by
  intro x hx
  simp only [HMinusOne.closedUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩
end
end AVenhance.Infra.Ergodic
