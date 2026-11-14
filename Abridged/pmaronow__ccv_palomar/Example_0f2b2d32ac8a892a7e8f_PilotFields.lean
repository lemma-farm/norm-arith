module

public import Mathlib

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_0f2b2d32ac8a892a7e8f_PilotFields ====
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

section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
def bilinear (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M


set_option linter.unusedVariables false in
theorem bilinear_section_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {y : Ω} (hy : MemLp (η y) 2 M) 
    (h_NearlyMinimax_PilotFields_operatorField_memLp : ∀ {W : Type u_2} {H : Type u_3} [inst : MeasurableSpace W] [inst_1 : NormedAddCommGroup H]
      [inst_2 : InnerProductSpace ℝ H] {M : MeasureTheory.Measure W} [MeasureTheory.IsFiniteMeasure M]
      [inst_4 : MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {B : W → H →L[ℝ] H},
      (Measurable fun (z : W × H) ↦ (B z.1 : H → H) z.2) →
        ∀ {C : ℝ},
          (∀ (w : W), ‖B w‖ ≤ C) →
            ∀ {f : W → H},
              Measurable f →
                MeasureTheory.MemLp f 2 M → MeasureTheory.MemLp (fun (w : W) ↦ (B w : H → H) (f w)) 2 M)
    (h_NearlyMinimax_PilotFields_operatorField_energy_le : ∀ {W : Type u_2} {H : Type u_3} [inst : MeasurableSpace W] [inst_1 : NormedAddCommGroup H]
      [inst_2 : InnerProductSpace ℝ H] {M : MeasureTheory.Measure W} [MeasureTheory.IsFiniteMeasure M]
      [inst_4 : MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {B : W → H →L[ℝ] H},
      (Measurable fun (z : W × H) ↦ (B z.1 : H → H) z.2) →
        ∀ {C : ℝ},
          0 ≤ C →
            (∀ (w : W), ‖B w‖ ≤ C) →
              ∀ {f : W → H},
                Measurable f →
                  MeasureTheory.MemLp f 2 M →
                    ∫ (w : W), ‖(B w : H → H) (f w)‖ ^ 2 ∂M ≤ C ^ 2 * ∫ (w : W), ‖f w‖ ^ 2 ∂M)
    :
    (∫ x, bilinear (M := M) η B (x, y) ^ 2 ∂μ) ≤
      lam * C ^ 2 * ∫ w, ‖η y w‖ ^ 2 ∂M := by
  have hm : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  have hv := h_NearlyMinimax_PilotFields_operatorField_memLp hmB hbound hm hy
  have hb := (htest (fun w => B w (η y w)) hv).trans
    (mul_le_mul_of_nonneg_left (h_NearlyMinimax_PilotFields_operatorField_energy_le hmB hC hbound hm hy) hlam)
  simpa only [test, bilinear, mul_assoc] using hb

end OperatorField
end NearlyMinimax.PilotFields
