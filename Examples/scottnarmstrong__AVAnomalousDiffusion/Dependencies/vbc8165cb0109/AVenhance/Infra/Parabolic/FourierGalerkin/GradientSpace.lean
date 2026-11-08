-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes
public import Mathlib
public import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The spatial `L²` gradient space for real Fourier cutoffs

This module places the explicitly differentiated real modes in the vector-valued torus `L²`
space and packages their finite synthesis as a continuous linear map. The Euclidean norm on the
two gradient coordinates is the `PiLp 2` norm, matching the gradient energy.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
local instance gradientSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance gradientSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance gradientSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Euclidean two-vectors with their usual squared-sum norm. -/
abbrev SpatialVector := PiLp 2 (fun _ : Fin 2 => ℝ)
/-- The Hilbert space of square-integrable spatial vector fields on the unit torus. -/
abbrev SpatialGradientL2 := Lp SpatialVector 2 (volume : Measure Torus)
def GradientSpace.closedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
theorem GradientSpace.isCompact_closedCell : IsCompact GradientSpace.closedCell := by
  simpa [GradientSpace.closedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
theorem GradientSpace.unitTorusRepresentative_mem_closedCell (x : Torus) :
    AVenhance.Infra.Torus.unitTorusRepresentative 2 x ∈ GradientSpace.closedCell := by
  simp only [GradientSpace.closedCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  have hi : AVenhance.Infra.Torus.unitTorusRepresentative 2 x i ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [AVenhance.Infra.Torus.unitTorusRepresentative] using
      (AddCircle.equivIoc (1 : ℝ) 0 (x i)).2
  exact ⟨le_of_lt hi.1, hi.2⟩
end AVenhance.Infra.Parabolic.FourierGalerkin
end
