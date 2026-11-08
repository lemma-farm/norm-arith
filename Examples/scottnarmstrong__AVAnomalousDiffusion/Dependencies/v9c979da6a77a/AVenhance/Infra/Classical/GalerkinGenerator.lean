-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.PeriodicCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinModeCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite Fourier generator identities used in the classical Galerkin estimates. -/
@[expose] public section
noncomputable section
open MeasureTheory
local instance classicalGeneratorMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalGeneratorMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalGeneratorProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.FourierGalerkin
open Homogenization
def GalerkinGenerator.generatorClosedUnitCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
theorem GalerkinGenerator.generator_closedUnitCell_compact :
    IsCompact GalerkinGenerator.generatorClosedUnitCell := by
  simpa [GalerkinGenerator.generatorClosedUnitCell] using
    (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc))
theorem exists_uniform_bound_of_continuous_periodic
    (f : Vec 2 → ℝ) (hf : Continuous f)
    (hper : AVenhance.IsZ2Periodic f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  let g : Vec 2 → ℝ := fun x => ‖f x‖
  have hcont : Continuous g := continuous_norm.comp hf
  have hupper : BddAbove (g '' GalerkinGenerator.generatorClosedUnitCell) :=
    GalerkinGenerator.generator_closedUnitCell_compact.bddAbove_image hcont.continuousOn
  let C₀ : ℝ := sSup (g '' GalerkinGenerator.generatorClosedUnitCell)
  have hcell_nonempty : (g '' GalerkinGenerator.generatorClosedUnitCell).Nonempty := by
    refine ⟨g (fun _ => (0 : ℝ)), (fun _ => (0 : ℝ)), ?_, rfl⟩
    simp only [GalerkinGenerator.generatorClosedUnitCell, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    intro i
    norm_num
  have hcell_bound (x : Vec 2) (hx : x ∈ GalerkinGenerator.generatorClosedUnitCell) :
      g x ≤ C₀ := le_csSup hupper ⟨x, hx, rfl⟩
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x
  let k : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let y : Vec 2 := x + AVenhance.latticeShift k
  have hyi (i : Fin 2) : y i = x i - (Int.floor (x i) : ℝ) := by
    dsimp [y, k, AVenhance.latticeShift]
    rw [Int.cast_neg]
    exact Int.self_sub_floor (a := (x i : ℝ))
  have hy : y ∈ GalerkinGenerator.generatorClosedUnitCell := by
    simp only [GalerkinGenerator.generatorClosedUnitCell, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    intro i
    rw [hyi]
    constructor
    · exact sub_nonneg.mpr (Int.floor_le (x i))
    · have hfloor := Int.lt_floor_add_one (x i)
      linarith
  have hperiod := hper k x
  have hbound := hcell_bound y hy
  change ‖f y‖ ≤ C₀ at hbound
  calc
    ‖f x‖ = ‖f y‖ := by rw [← hperiod]
    _ ≤ C₀ := hbound
    _ ≤ max C₀ 0 := le_max_left _ _
/-- The torus representative of a continuous periodic scalar is square-integrable. -/
theorem memLp_periodicToTorus_real {f : Vec 2 → ℝ}
    (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2
      (volume : Measure Torus) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_of_continuous_periodic f hf hper
  have hmeas : Measurable (AVenhance.Infra.Torus.periodicToTorus f) :=
    hf.measurable.comp
      (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
  have hpoint : ∀ᵐ x : Torus, ‖AVenhance.Infra.Torus.periodicToTorus f x‖ ≤ C := by
    filter_upwards with x
    exact hbound (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
  exact MemLp.of_bound hmeas.aestronglyMeasurable C hpoint
end AVenhance.Infra.Classical
end
