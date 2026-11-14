module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Int.Interval
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v27b0e38dca4f.Critical2DKPZ.WalkTails.Hypergeometric ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The squared-binomial walk law

The normalized squared-binomial weights form a hypergeometric law.
Through the increment `2j-m`, they describe the common endpoint of two independent simple walks
conditioned to have the same endpoint after `m` steps.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.WalkTails
open Finset.Nat Finset.HasAntidiagonal
/-- The finite hypergeometric mass at `j`: the squared binomial law on
`{0, ..., m}`.  It is zero outside that interval. -/
def hypergeometricWeight (m j : ℕ) : ℝ :=
  ((Nat.choose m j : ℝ) ^ 2) / (Nat.choose (2 * m) m : ℝ)

end Critical2DKPZ.WalkTails
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_da9c80f65fe03028b22e_PairBlockIncrementProfile ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Local central limit estimates for pair-block increments -/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter

/-- The sampled Gaussian approximation to one hypergeometric increment. -/
def sampledHypergeometricGaussianWeight (m k : ℕ) : ℝ :=
  (2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
    Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))
/-- The sampled Gaussian profile normalized by its finite mass on the support. -/
def normalizedSampledHypergeometricGaussianWeight (m k : ℕ) : ℝ :=
  sampledHypergeometricGaussianWeight m k /
    (∑ j ∈ Finset.range (m + 1), sampledHypergeometricGaussianWeight m j)


set_option linter.unusedVariables false in
/-- The normalized sampled Gaussian comparison has a pointwise error of
order `1/m` against one exact squared-binomial block. -/
theorem exists_hypergeometricWeight_normalizedGaussian_point_error 
    (h_Critical2DKPZ_SHF_Moments_exists_hypergeometricWeight_localGaussian_error : ∃ (C : ℝ),
      0 < C ∧
        ∃ (m₀ : ℕ),
          ∀ (m : ℕ),
            m₀ ≤ m →
              ∀ k ≤ m,
                |√(↑m : ℝ) * Critical2DKPZ.WalkTails.hypergeometricWeight m k -
                      2 / √Real.pi * Real.exp (-(2 * (↑k : ℝ) - (↑m : ℝ)) ^ 2 / (↑m : ℝ))| ≤
                  C / (↑m : ℝ))
    (h_Critical2DKPZ_SHF_Moments_hypergeometricWeightGaussianProfile_bounds : ∀ (m k : ℕ),
      1 ≤ m →
        0 ≤ 2 / √Real.pi * Real.exp (-(2 * (↑k : ℝ) - (↑m : ℝ)) ^ 2 / (↑m : ℝ)) ∧
          2 / √Real.pi * Real.exp (-(2 * (↑k : ℝ) - (↑m : ℝ)) ^ 2 / (↑m : ℝ)) ≤ 2)
    (h_Critical2DKPZ_SHF_Moments_exists_hypergeometricGaussian_mass_error : ∃ (C : ℝ),
      0 < C ∧
        ∃ (m₀ : ℕ),
          ∀ (m : ℕ),
            m₀ ≤ m →
              |∑ k ∈ Finset.range (m + 1),
                      2 / √Real.pi / √(↑m : ℝ) * Real.exp (-(2 * (↑k : ℝ) - (↑m : ℝ)) ^ 2 / (↑m : ℝ)) -
                    1| ≤
                C / √(↑m : ℝ))
    :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ ∀ k : ℕ, k ≤ m →
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k| ≤ C / (m : ℝ) := by
  obtain ⟨C₁, hC₁, m₁, hprofile⟩ := h_Critical2DKPZ_SHF_Moments_exists_hypergeometricWeight_localGaussian_error
  obtain ⟨C₂, hC₂, m₂, hMass⟩ := h_Critical2DKPZ_SHF_Moments_exists_hypergeometricGaussian_mass_error
  have hsqrtT : Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ m : ℕ in atTop, C₂ / Real.sqrt (m : ℝ) < 1 / 2 := by
    filter_upwards [hsqrtT.eventually_gt_atTop (2 * C₂)] with m hm
    have hroot : 0 < Real.sqrt (m : ℝ) := lt_trans (by positivity) hm
    rw [div_lt_iff₀ hroot]
    nlinarith [hm]
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hsmall
  let m₀ : ℕ := max 1 (max m₁ (max m₂ M))
  have hm₁le : m₁ ≤ m₀ := by simp [m₀]
  have hm₂le : m₂ ≤ m₀ := by simp [m₀]
  have hmMle : M ≤ m₀ := by simp [m₀]
  refine ⟨C₁ + 4 * C₂, by positivity, m₀, ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := le_trans (by simp [m₀]) hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hrootOne : 1 ≤ Real.sqrt (m : ℝ) := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hm1)
  have hlocal := hprofile m (le_trans hm₁le hm)
  have hMassm := hMass m (le_trans hm₂le hm)
  have hsmallm : C₂ / Real.sqrt (m : ℝ) < 1 / 2 := hM m (le_trans hmMle hm)
  let g : ℕ → ℝ := sampledHypergeometricGaussianWeight m
  let Z : ℝ := ∑ j ∈ Finset.range (m + 1), g j
  have hZdist : |Z - 1| ≤ C₂ / Real.sqrt (m : ℝ) := by
    simpa [Z, g, sampledHypergeometricGaussianWeight] using hMassm
  have hZlower : 1 / 2 ≤ Z := by
    have hlow := (abs_le.mp hZdist).1
    linarith
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZlower
  have hZinv : Z⁻¹ ≤ 2 := by
    rw [← one_div]
    rw [div_le_iff₀ hZpos]
    linarith
  have hG (k : ℕ) :
      0 ≤ 2 / Real.sqrt Real.pi *
        Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) ∧
      2 / Real.sqrt Real.pi *
        Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) ≤ 2 :=
    h_Critical2DKPZ_SHF_Moments_hypergeometricWeightGaussianProfile_bounds m k hm1
  have hpoint (k : ℕ) (hk : k ≤ m) :
      |WalkTails.hypergeometricWeight m k - g k| ≤
        C₁ / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
    let G : ℝ := 2 / Real.sqrt Real.pi *
      Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))
    have hscaled := hlocal k hk
    have hg : g k = G / Real.sqrt (m : ℝ) := by
      dsimp [g, G, sampledHypergeometricGaussianWeight]
      ring
    have hEq : WalkTails.hypergeometricWeight m k - g k =
        (Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k - G) /
          Real.sqrt (m : ℝ) := by
      rw [hg]
      field_simp [hsqrt.ne']
    rw [hEq, abs_div, abs_of_pos hsqrt]
    calc
      |Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k - G| /
          Real.sqrt (m : ℝ) ≤ (C₁ / (m : ℝ)) / Real.sqrt (m : ℝ) :=
            div_le_div_of_nonneg_right hscaled (by positivity)
      _ = C₁ / ((m : ℝ) * Real.sqrt (m : ℝ)) := by ring
  have hcorrect (k : ℕ) :
      |g k - g k / Z| = g k * |Z - 1| * Z⁻¹ := by
    have hg0 : 0 ≤ g k := by dsimp [g, sampledHypergeometricGaussianWeight]; positivity
    calc
      |g k - g k / Z| = |g k * (Z - 1) / Z| := by
        congr 1
        field_simp [hZpos.ne']
      _ = |g k * (Z - 1)| / Z := by rw [abs_div, abs_of_pos hZpos]
      _ = g k * |Z - 1| * Z⁻¹ := by
        rw [abs_mul, abs_of_nonneg hg0]
        ring
  have hrawUpper (k : ℕ) : g k ≤ 2 / Real.sqrt (m : ℝ) := by
    have hGupper := (hG k).2
    have hEq : g k =
        (2 / Real.sqrt Real.pi *
          Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))) /
          Real.sqrt (m : ℝ) := by
      dsimp [g, sampledHypergeometricGaussianWeight]
      ring
    rw [hEq]
    exact div_le_div_of_nonneg_right hGupper hsqrt.le
  have hcorrection (k : ℕ) : |g k - g k / Z| ≤ 4 * C₂ / (m : ℝ) := by
    have hg0 : 0 ≤ g k := by dsimp [g, sampledHypergeometricGaussianWeight]; positivity
    have habs : 0 ≤ |Z - 1| := abs_nonneg _
    have hfirstProd : g k * |Z - 1| ≤
        (2 / Real.sqrt (m : ℝ)) * (C₂ / Real.sqrt (m : ℝ)) :=
      mul_le_mul (hrawUpper k) hZdist habs (by positivity)
    have hZinv0 : 0 ≤ Z⁻¹ := inv_nonneg.mpr hZpos.le
    have hsecondProd : g k * |Z - 1| * Z⁻¹ ≤
        ((2 / Real.sqrt (m : ℝ)) * (C₂ / Real.sqrt (m : ℝ))) * 2 :=
      mul_le_mul hfirstProd hZinv hZinv0 (by positivity)
    rw [hcorrect k]
    calc
      g k * |Z - 1| * Z⁻¹ ≤
          (2 / Real.sqrt (m : ℝ)) * (C₂ / Real.sqrt (m : ℝ)) * 2 := by
            simpa [mul_assoc] using hsecondProd
      _ = 4 * C₂ / (m : ℝ) := by
        field_simp [hsqrt.ne', hmR.ne']
        rw [Real.sq_sqrt hmR.le]
        ring
  have hfirst : C₁ / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ C₁ / (m : ℝ) := by
    have hden : (m : ℝ) ≤ (m : ℝ) * Real.sqrt (m : ℝ) := by
      nlinarith [hmR.le, hrootOne]
    exact div_le_div_of_nonneg_left hC₁.le hmR hden
  constructor
  · exact hm1
  · intro k hk
    have hpoint' : |WalkTails.hypergeometricWeight m k - g k| ≤ C₁ / (m : ℝ) :=
      le_trans (hpoint k hk) hfirst
    have hnormalized :
        normalizedSampledHypergeometricGaussianWeight m k = g k / Z := rfl
    calc
      |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k| ≤
        |WalkTails.hypergeometricWeight m k - g k| + |g k - g k / Z| := by
          rw [hnormalized]
          calc
            _ = |(WalkTails.hypergeometricWeight m k - g k) + (g k - g k / Z)| := by
              congr 1
              ring
            _ ≤ _ := abs_add_le _ _
      _ ≤ C₁ / (m : ℝ) + 4 * C₂ / (m : ℝ) :=
        add_le_add hpoint' (hcorrection k)
      _ = (C₁ + 4 * C₂) / (m : ℝ) := by ring
end Critical2DKPZ.SHF.Moments
end
