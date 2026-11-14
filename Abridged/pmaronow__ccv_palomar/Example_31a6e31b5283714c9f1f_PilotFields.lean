module

public import Mathlib

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb054b8e19151.NearlyMinimax.PilotFluctuation ====
public section
@[expose] public section
/-! Independent pilot fluctuation estimates. These estimates integrate the
actual product law of the two pilots; no bilinear variance estimate is assumed. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFluctuation
set_option backward.isDefEq.respectTransparency false
variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

axiom three_square_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)

end NearlyMinimax.PilotFluctuation

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_31a6e31b5283714c9f1f_PilotFields ====
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

axiom test_sq_integrable {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    Integrable (fun x => test (M := M) η v x ^ 2) μ

section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
def bilinear (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M

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
axiom bilinear_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ) ≤
      lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M

def fluctuation (η : Ω → W → H) (B : W → H →L[ℝ] H)
    (v₁ v₂ : W → H) (z : Ω × Ω) : ℝ :=
  test (M := M) η v₁ z.1 + test (M := M) η v₂ z.2 + bilinear (M := M) η B z
axiom fluctuation_memLp_two {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    MemLp (fluctuation (M := M) η B v₁ v₂) 2 (μ.prod μ)
theorem fluctuation_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    (∫ z, fluctuation (M := M) η B v₁ v₂ z ^ 2 ∂μ.prod μ) ≤
      3 * lam * ((∫ w, ‖v₁ w‖ ^ 2 ∂M) + (∫ w, ‖v₂ w‖ ^ 2 ∂M) +
        C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have h₁ := (test_sq_integrable hη hv₁).comp_fst μ
  have h₂ := (test_sq_integrable hη hv₂).comp_snd μ
  have h₃ := bilinear_sq_integrable hmη hη hmB hC hlam hbound htest
  calc
    _ ≤ ∫ z : Ω × Ω, 3 * (test (M := M) η v₁ z.1 ^ 2 +
        test (M := M) η v₂ z.2 ^ 2 + bilinear (M := M) η B z ^ 2) ∂μ.prod μ := by
      exact integral_mono
        (fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hv₁ hv₂).integrable_sq
        (((h₁.add h₂).add h₃).const_mul 3)
        (fun _ => PilotFluctuation.three_square_le _ _ _)
    _ = 3 * ((∫ x, test (M := M) η v₁ x ^ 2 ∂μ) +
        (∫ x, test (M := M) η v₂ x ^ 2 ∂μ) +
        (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ)) := by
      have ha := integral_add (h₁.add h₂) h₃
      have hb := integral_add h₁ h₂
      simp only [Pi.add_apply] at ha hb
      rw [integral_const_mul, ha, hb,
        integral_fun_fst (μ := μ) (ν := μ) (fun x => test (M := M) η v₁ x ^ 2),
        integral_fun_snd (μ := μ) (ν := μ) (fun x => test (M := M) η v₂ x ^ 2)]
      simp
    _ ≤ 3 * (lam * (∫ w, ‖v₁ w‖ ^ 2 ∂M) + lam * (∫ w, ‖v₂ w‖ ^ 2 ∂M) +
        lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
      gcongr
      · exact htest v₁ hv₁
      · exact htest v₂ hv₂
      · exact bilinear_energy_le hmη hη hmB hC hlam hbound htest
    _ = _ := by ring
end OperatorField
end NearlyMinimax.PilotFields
