-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Heat.WeakFourier
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.Density
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Classical.GalerkinModeCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteGalerkinEnergy
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Fourier projection of periodic weak gradients

The weak-gradient Fourier multiplier identifies the derivative of each real Fourier
projection with the real Fourier projection of the weak gradient. This gives the slice-wise
`H¹` convergence needed in the weak energy passage.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
namespace AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin
local instance weakProjectionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakProjectionMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakProjectionProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakProjectionProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
open AVenhance.Infra.Classical
theorem weakProjection_realCellToTorus_memLp {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2 volume := by
  have hcell : MemLp f 2
      (volume.restrict (AVenhance.Infra.Torus.unitCell 2)) := by
    rw [Measure.restrict_congr_set
      AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
    exact hf
  let Cell := {x : Vec 2 // x ∈ AVenhance.Infra.Torus.unitCell 2}
  let μCell : Measure Cell := volume.comap (Subtype.val : Cell → Vec 2)
  have hmpSub : MeasurePreserving (Subtype.val : Cell → Vec 2) μCell
      (volume.restrict (AVenhance.Infra.Torus.unitCell 2)) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (AVenhance.Infra.Torus.measurableSet_unitCell 2) volume]
  have hsub : MemLp (fun x : Cell => f x.1) 2 μCell := by
    exact hcell.comp_measurePreserving hmpSub
  have hmp := UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin 2 => (0 : ℝ))
  have htorus := hsub.comp_measurePreserving hmp
  have heq : AVenhance.Infra.Torus.periodicToTorus f =
      fun y => (fun x : Cell => f x.1)
        (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ)) y) := by
    funext y
    rfl
  rw [heq]
  exact htorus
end AVenhance.Infra.Parabolic.WeakUniqueness
end
