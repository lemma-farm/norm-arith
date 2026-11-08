/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.Defs.IsCircleAverage
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.Defs.IsEquatorGFF
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.GFFStructure.GaussianClosure
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite circle-average families are jointly Gaussian, by Gaussian closure of the field. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs
/-- Every finite family of circle averages of an equator GFF is centered jointly Gaussian. -/
theorem circleAverage_finite_family_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (p : ι → ℂ × ℝ) :
    IsCenteredJointlyGaussian P (fun ω i => Xc ω (p i).1 (p i).2) := by
  obtain ⟨hProcess, hMean⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  refine ⟨hX.1, ?_, ?_⟩
  · intro i
    exact hProcess.aemeasurable (p i)
  · intro a
    let S : Ω → ℝ := fun ω => ∑ i, a i * Xc ω (p i).1 (p i).2
    have hWeighted : IsGaussianProcess
        (fun i => fun ω => a i * Xc ω (p i).1 (p i).2) P := by
      have hParam : IsGaussianProcess
          (fun i => fun ω => Xc ω (p i).1 (p i).2) P := by
        simpa only [Function.comp_def] using hProcess.comp_right p
      simpa only [smul_eq_mul] using hParam.smul a
    have hLaw : HasGaussianLaw S P := by
      simpa only [S, smul_eq_mul] using
        hWeighted.hasGaussianLaw_fun_sum (I := Finset.univ)
    have hMeanS : (∫ ω, S ω ∂P) = 0 := by
      dsimp [S]
      rw [integral_finsetSum]
      · simp only [integral_const_mul, hMean, mul_zero, Finset.sum_const_zero]
      · intro i hi
        exact (hProcess.hasGaussianLaw_eval (p i)).integrable.const_mul (a i)
    refine ⟨hLaw.memLp_two, ?_⟩
    refine ⟨(Var[S; P]).toNNReal, ?_⟩
    simpa only [hMeanS] using hLaw.map_eq_gaussianReal
end DOZZ.Proofs
