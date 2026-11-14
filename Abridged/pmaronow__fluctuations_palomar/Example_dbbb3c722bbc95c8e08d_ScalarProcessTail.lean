module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v5bb58cb42820.SKConstants.ScalarProcessKernel ====
public section
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SKConstants

noncomputable def scalarKernel (z : ℝ) (t : ℝ≥0) (y : ℝ) : ℝ :=
  Real.exp (-(t : ℝ) / ((2 : ℕ) : ℝ)) * gaussianPDFReal z t y *
    Real.cosh y / Real.cosh z

noncomputable def scalarKernelLaw (z : ℝ) (t : ℝ≥0) : Measure ℝ :=
  volume.withDensity (fun y ↦ ENNReal.ofReal (scalarKernel z t y))

end SKConstants

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Examples.Example_dbbb3c722bbc95c8e08d_ScalarProcessTail ====
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace SKConstants
noncomputable def scalarDefect (y : ℝ) : ℝ := 1 - (Real.tanh y) ^ 2
noncomputable def scalarP (z : ℝ) (t : ℝ≥0) : ℝ :=
  ∫ y, scalarDefect y ∂scalarKernelLaw z t


set_option linter.unusedVariables false in
theorem scalarP_le_sharp_tail (z : ℝ) (t : ℝ≥0) 
    (h_SKConstants_integrable_gaussian_div_cosh : ∀ (z : ℝ) (t : NNReal),
      MeasureTheory.Integrable (fun (y : ℝ) ↦ ProbabilityTheory.gaussianPDFReal z t y / Real.cosh y)
        MeasureTheory.MeasureSpace.volume)
    (h_SKConstants_integral_inv_cosh_le_four : ∫ (y : ℝ), 1 / Real.cosh y ≤ 4)
    (h_SKConstants_gaussianPDFReal_le_prefactor : ∀ (z y : ℝ) (t : NNReal), ProbabilityTheory.gaussianPDFReal z t y ≤ (√(2 * Real.pi * (↑t : ℝ)))⁻¹)
    (h_SKConstants_integrable_inv_cosh : MeasureTheory.Integrable (fun (y : ℝ) ↦ 1 / Real.cosh y) MeasureTheory.MeasureSpace.volume)
    (h_SKConstants_scalarP_eq_gaussian_integral : ∀ (z : ℝ) (t : NNReal),
      SKConstants.scalarP z t =
        Real.exp (-(↑t : ℝ) / 2) / Real.cosh z *
          ∫ (y : ℝ), ProbabilityTheory.gaussianPDFReal z t y / Real.cosh y)
    :
    scalarP z t ≤ 4 * (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
      (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ := by
  rw [h_SKConstants_scalarP_eq_gaussian_integral]
  have hg : (∫ y, gaussianPDFReal z t y / Real.cosh y) ≤
      (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ * 4 := by
    calc
      _ ≤ ∫ y, (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ * (1 / Real.cosh y) := by
        apply integral_mono (h_SKConstants_integrable_gaussian_div_cosh z t)
          (h_SKConstants_integrable_inv_cosh.const_mul _)
        intro y
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right (h_SKConstants_gaussianPDFReal_le_prefactor z y t)
            (inv_nonneg.mpr (Real.cosh_pos y).le)
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left h_SKConstants_integral_inv_cosh_le_four (by positivity)
  have hh := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ Real.exp (-(t : ℝ) / 2) / Real.cosh z by positivity)
  convert hh using 1
  ring

end SKConstants
