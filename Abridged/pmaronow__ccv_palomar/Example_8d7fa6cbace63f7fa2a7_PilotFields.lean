module

public import Mathlib

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_8d7fa6cbace63f7fa2a7_PilotFields ====
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

section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]


set_option linter.unusedVariables false in
theorem operatorField_energy_le {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M) 
    (h_NearlyMinimax_PilotFields_operatorField_memLp : ∀ {W : Type u_2} {H : Type u_3} [inst : MeasurableSpace W] [inst_1 : NormedAddCommGroup H]
      [inst_2 : InnerProductSpace ℝ H] {M : MeasureTheory.Measure W} [MeasureTheory.IsFiniteMeasure M]
      [inst_4 : MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {B : W → H →L[ℝ] H},
      (Measurable fun (z : W × H) ↦ (B z.1 : H → H) z.2) →
        ∀ {C : ℝ},
          (∀ (w : W), ‖B w‖ ≤ C) →
            ∀ {f : W → H},
              Measurable f →
                MeasureTheory.MemLp f 2 M → MeasureTheory.MemLp (fun (w : W) ↦ (B w : H → H) (f w)) 2 M)
    :
    (∫ w, ‖B w (f w)‖ ^ 2 ∂M) ≤ C ^ 2 * ∫ w, ‖f w‖ ^ 2 ∂M := by
  rw [← integral_const_mul]
  apply integral_mono (h_NearlyMinimax_PilotFields_operatorField_memLp hmB hbound hmf hf).norm.integrable_sq
    (hf.norm.integrable_sq.const_mul (C ^ 2))
  intro w
  calc
    ‖B w (f w)‖ ^ 2 ≤ (C * ‖f w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (((B w).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))) 2
    _ = C ^ 2 * ‖f w‖ ^ 2 := by ring

end OperatorField
end NearlyMinimax.PilotFields
