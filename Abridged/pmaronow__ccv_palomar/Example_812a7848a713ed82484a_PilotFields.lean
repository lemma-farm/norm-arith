module

public import Mathlib

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_812a7848a713ed82484a_PilotFields ====
@[expose] public section
/-! Pilot fields remain ordinary jointly measurable functions. The scalar
test and independent-pilot bounds below do not assume measurability of a
random map into an L² quotient space. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

def test (η : Ω → W → H) (v : W → H) (x : Ω) : ℝ :=
  ∫ w, ⟪η x w, v w⟫ ∂M
axiom memLp_sections {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M)) :
    ∀ᵐ x ∂μ, MemLp (η x) 2 M

section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
def bilinear (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M

axiom bilinear_section_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {y : Ω} (hy : MemLp (η y) 2 M) :
    (∫ x, bilinear (M := M) η B (x, y) ^ 2 ∂μ) ≤
      lam * C ^ 2 * ∫ w, ‖η y w‖ ^ 2 ∂M
axiom bilinear_sq_integrable {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    Integrable (fun z => bilinear (M := M) η B z ^ 2) (μ.prod μ)
/-- The integrated test estimate supplies the bilinear fluctuation bound
for the actual product of two jointly measurable pilot fields. -/
theorem bilinear_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ) ≤
      lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M := by
  have hZ := bilinear_sq_integrable hmη hη hmB hC hlam hbound htest
  rw [integral_prod_symm _ hZ]
  calc
    _ ≤ ∫ y, lam * C ^ 2 * (∫ w, ‖η y w‖ ^ 2 ∂M) ∂μ := by
      apply integral_mono_ae hZ.integral_prod_right
        (hη.norm.integrable_sq.integral_prod_left.const_mul (lam * C ^ 2))
      filter_upwards [memLp_sections hη] with y hy
      exact bilinear_section_energy_le hmη hmB hC hlam hbound htest hy
    _ = _ := by
      rw [integral_const_mul, integral_prod _ hη.norm.integrable_sq]

end OperatorField
end NearlyMinimax.PilotFields
