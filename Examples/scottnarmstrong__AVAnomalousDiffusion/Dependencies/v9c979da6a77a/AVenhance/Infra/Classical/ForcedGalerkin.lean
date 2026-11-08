-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.Energy
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.ODE.Linear.Energy
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Energy data for finite Galerkin ODEs with an integrable forcing. -/
@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVenhance.Infra.Classical
/-- A finite weak-form Galerkin system together with a coefficient-side forcing. -/
structure EnergyWeakFormData (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  coefficient : ℝ → E →L[ℝ] E
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficient_aestronglyMeasurable : AEStronglyMeasurable coefficient volume
  coefficient_norm_le : ∀ t, ‖coefficient t‖ ≤ coefficientBound
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  gradient : E →L[ℝ] G
  driftBound : ℝ
  driftForm : ℝ → E → ℝ
  weakForm_energy : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ c,
    2 * inner ℝ c (coefficient t c) =
      -2 * driftForm t c - 2 * diffusivity * ‖gradient c‖ ^ 2
  drift_bound : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ c,
    |driftForm t c| ≤ driftBound * ‖gradient c‖ * ‖c‖
structure ForcedGalerkinData (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  weak : EnergyWeakFormData E G
  initial : E
  forcing : ℝ → E
  forcing_integrable : IntervalIntegrable forcing volume 0 1
namespace ForcedGalerkinData
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
end ForcedGalerkinData
namespace ForcedGalerkinData
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
end ForcedGalerkinData
end AVenhance.Infra.Classical
end
