module

public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.Moments.SubGaussian

-- ==== Examples.pmaronow__slowequilibration_palomar.Examples.Example_bb89f01bafb2ee9b12a0_CommonHessianSubgaussianHighMoments ====
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! Genuine every-real-q ordinary moments from the actual two-sided
sub-Gaussian moment generating function at a chosen scaling. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
def subgaussianMomentConstant (q B:ℝ):ℝ:=1+2*((Nat.ceil q).factorial:ℝ)*Real.exp B
set_option linter.unusedVariables false in
theorem subgaussian_high_moment {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω)
    [IsProbabilityMeasure P] (F:Ω→ℝ) (hF:Measurable F) {c:ℝ≥0}
    (hG:HasSubgaussianMGF F c P) {t B:ℝ} (ht:0<t)
    (hBudget:(c:ℝ)*t^2/2≤B) (q:ℝ) (hq:0≤q) 
    (h_SlowEquilibration_NonnegativeRealMoment_real_moment_of_integer : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (f : Ω → ℝ),
      Measurable f →
        (∀ (x : Ω), 0 ≤ f x) →
          ∀ {q : ℝ},
            0 ≤ q →
              ∀ (r : ℕ),
                q ≤ (↑r : ℝ) →
                  MeasureTheory.Integrable (fun (x : Ω) ↦ f x ^ r) μ →
                    MeasureTheory.Integrable (fun (x : Ω) ↦ f x ^ q) μ ∧
                      ∫ (x : Ω), f x ^ q ∂μ ≤ 1 + ∫ (x : Ω), f x ^ r ∂μ)
    (h_SlowEquilibration_GaussianQuadraticVariance_integer_absolute_moment_of_exponential : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (f : Ω → ℝ),
      Measurable f →
        ∀ (r : ℕ),
          MeasureTheory.Integrable (fun (x : Ω) ↦ Real.exp (f x)) μ →
            MeasureTheory.Integrable (fun (x : Ω) ↦ Real.exp (-f x)) μ →
              MeasureTheory.Integrable (fun (x : Ω) ↦ |f x| ^ r) μ ∧
                ∫ (x : Ω), |f x| ^ r ∂μ ≤
                  (↑r.factorial : ℝ) * (∫ (x : Ω), Real.exp (f x) ∂μ + ∫ (x : Ω), Real.exp (-f x) ∂μ))
    :
    Integrable (fun x=>|F x|^q) P ∧
      (∫ x,|F x|^q ∂P) ≤ subgaussianMomentConstant q B/t^q:=by
  let f:=fun x=>t*F x
  have hf:Measurable f:=measurable_const.mul hF
  have hPos:Integrable (fun x=>Real.exp (f x)) P:=hG.integrable_exp_mul t
  have hNeg:Integrable (fun x=>Real.exp (-f x)) P:=by
    simpa only [f,neg_mul] using hG.integrable_exp_mul (-t)
  have hPosBound:(∫ x,Real.exp (f x) ∂P)≤Real.exp B:=
    (hG.mgf_le t).trans (Real.exp_le_exp.mpr hBudget)
  have hNegBound:(∫ x,Real.exp (-f x) ∂P)≤Real.exp B:=by
    have hh:=(hG.mgf_le (-t)).trans (Real.exp_le_exp.mpr (by simpa only [neg_sq] using hBudget))
    simpa only [mgf,f,neg_mul] using hh
  have hInt:=h_SlowEquilibration_GaussianQuadraticVariance_integer_absolute_moment_of_exponential P f hf (Nat.ceil q) hPos hNeg
  have hIntBound:(∫ x,|f x|^(Nat.ceil q) ∂P)≤2*((Nat.ceil q).factorial:ℝ)*Real.exp B:=by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hPosBound hNegBound)
      (Nat.cast_nonneg (Nat.ceil q).factorial)
    exact hInt.2.trans (by nlinarith [hh])
  have hReal:=h_SlowEquilibration_NonnegativeRealMoment_real_moment_of_integer P (fun x=>|f x|) hf.abs
    (fun _=>abs_nonneg _) hq (Nat.ceil q) (Nat.le_ceil q) hInt.1
  have hBound:(∫ x,|f x|^q ∂P) ≤ subgaussianMomentConstant q B:=
    hReal.2.trans (add_le_add le_rfl hIntBound)
  have hEq (x):|F x|^q=(t^q)⁻¹*|f x|^q:=by
    dsimp only [f]
    rw [abs_mul,abs_of_pos ht,Real.mul_rpow ht.le (abs_nonneg _)]
    field_simp
  refine ⟨by simpa only [hEq] using hReal.1.const_mul ((t^q)⁻¹),?_⟩
  simp only [hEq,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hBound (by positivity)).trans_eq (by ring)
end
end SlowEquilibration.GaussianQuadraticVariance
