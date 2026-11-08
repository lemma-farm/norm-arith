module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrthogonalityKernelCrossFubini
public import Mathlib
set_option autoImplicit false
/-! # Actual unlinked Fourier cross integrals retain all four true cell masses -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace FalconerThetaGauge
open GaugeFrostman
theorem ae_mem_four_carriers (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁]
    [IsFiniteMeasure ρ₂] {X X' Y Y' : Set Plane} (hX : MeasurableSet X)
    (hX' : MeasurableSet X') (hY : MeasurableSet Y) (hY' : MeasurableSet Y') :
    ∀ᵐ p : (Plane × Plane) × (Plane × Plane)
      ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod ((ρ₂.restrict Y).prod (ρ₂.restrict Y')),
      p ∈ (X ×ˢ X') ×ˢ (Y ×ˢ Y') := by
  have h₁ : ∀ᵐ p ∂(ρ₁.restrict X).prod (ρ₁.restrict X'), p ∈ X ×ˢ X' := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (hX.prod hX')).mpr
    filter_upwards [ae_restrict_mem hX] with x hx
    filter_upwards [ae_restrict_mem hX'] with x' hx'
    exact ⟨hx, hx'⟩
  have h₂ : ∀ᵐ p ∂(ρ₂.restrict Y).prod (ρ₂.restrict Y'), p ∈ Y ×ˢ Y' := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (hY.prod hY')).mpr
    filter_upwards [ae_restrict_mem hY] with y hy
    filter_upwards [ae_restrict_mem hY'] with y' hy'
    exact ⟨hy, hy'⟩
  apply (Measure.ae_prod_mem_iff_ae_ae_mem ((hX.prod hX').prod (hY.prod hY'))).mpr
  filter_upwards [h₁] with p hp
  filter_upwards [h₂] with q hq
  exact ⟨hp, hq⟩
theorem integrable_complex_cross_of_memLp_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ f x * star (g x)) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono
  · exact hf.aestronglyMeasurable.mul hg.aestronglyMeasurable.star
  · filter_upwards [] with x
    simp only [norm_mul, norm_star, Pi.mul_apply, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), le_refl]
end FalconerThetaGauge
