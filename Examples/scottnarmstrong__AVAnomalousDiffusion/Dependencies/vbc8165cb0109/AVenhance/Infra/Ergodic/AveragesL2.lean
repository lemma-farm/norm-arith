-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Ergodic.AveragesL1
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The corrected L² ergodic estimate -/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus
noncomputable section
def AveragesL2.closedUnitCube (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1
theorem AveragesL2.unitCell_subset_closedUnitCube (d : ℕ) :
    Torus.unitCell d ⊆ AveragesL2.closedUnitCube d := by
  intro x hx
  simp only [AveragesL2.closedUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩
theorem AveragesL2.isCompact_closedUnitCube (d : ℕ) : IsCompact (AveragesL2.closedUnitCube d) := by
  simpa [AveragesL2.closedUnitCube] using isCompact_univ_pi fun _ : Fin d => isCompact_Icc
theorem continuous_unitCell_integrable {d : ℕ} {u : Vec d → ℝ}
    (hu : Continuous u) : IntegrableOn u (Torus.unitCell d) (volume : Measure (Vec d)) := by
  exact (hu.continuousOn.integrableOn_compact (AveragesL2.isCompact_closedUnitCube d)).mono_set
    (AveragesL2.unitCell_subset_closedUnitCube d)
end
end AVenhance.Infra.Ergodic
