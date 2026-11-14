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

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v4274b53974a7.Critical2DKPZ.WalkTails.Hypergeometric ====
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

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_503cc84957fc725f7742_PairBlockIncrementProfile ====
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


set_option linter.unusedVariables false in
/-- Normalizing the sampled Gaussian profile by its finite lattice mass gives
a probability law which remains `O(m⁻¹ᐟ²)`-close in discrete `L¹` to the
exact one-increment law. -/
theorem exists_normalized_hypergeometricGaussian_L1_error 
    (h_Critical2DKPZ_SHF_Moments_exists_hypergeometricGaussian_mass_error : ∃ (C : ℝ),
      0 < C ∧
        ∃ (m₀ : ℕ),
          ∀ (m : ℕ),
            m₀ ≤ m →
              |∑ k ∈ Finset.range (m + 1),
                      2 / √Real.pi / √(↑m : ℝ) * Real.exp (-(2 * (↑k : ℝ) - (↑m : ℝ)) ^ 2 / (↑m : ℝ)) -
                    1| ≤
                C / √(↑m : ℝ))
    (h_Critical2DKPZ_SHF_Moments_exists_hypergeometricWeight_gaussianL1_error : ∃ (C : ℝ),
      0 < C ∧
        ∃ (m₀ : ℕ),
          ∀ (m : ℕ),
            m₀ ≤ m →
              ∑ k ∈ Finset.range (m + 1),
                  |Critical2DKPZ.WalkTails.hypergeometricWeight m k -
                      2 / √Real.pi / √(↑m : ℝ) * Real.exp (-(2 * (↑k : ℝ) - (↑m : ℝ)) ^ 2 / (↑m : ℝ))| ≤
                C / √(↑m : ℝ))
    :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 1 ≤ m ∧
      0 < (∑ k ∈ Finset.range (m + 1),
          (2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
            Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))) ∧
      (∑ k ∈ Finset.range (m + 1),
        ((2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
            Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))) /
          (∑ j ∈ Finset.range (m + 1),
            (2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
              Real.exp (-(2 * (j : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)))) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          ((2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
            Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))) /
            (∑ j ∈ Finset.range (m + 1),
              (2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
                Real.exp (-(2 * (j : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)))|) ≤
        C / Real.sqrt (m : ℝ) := by
  obtain ⟨C₁, hC₁, m₁, hL1⟩ := h_Critical2DKPZ_SHF_Moments_exists_hypergeometricWeight_gaussianL1_error
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
  refine ⟨C₁ + C₂, by positivity, m₀, ?_⟩
  intro m hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hL := hL1 m (le_trans hm₁le hm)
  have hE := hMass m (le_trans hm₂le hm)
  have hsmallm : C₂ / Real.sqrt (m : ℝ) < 1 / 2 :=
    hM m (le_trans hmMle hm)
  let g : ℕ → ℝ := fun k =>
    (2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) *
      Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))
  let Z : ℝ := ∑ k ∈ Finset.range (m + 1), g k
  have hZpos : 0 < Z := by
    have hlow := (abs_le.mp hE).1
    dsimp [Z, g]
    linarith [hsmallm]
  have hZsum : (∑ k ∈ Finset.range (m + 1), g k / Z) = 1 := by
    dsimp [Z]
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hnormalized (k : ℕ) :
      WalkTails.hypergeometricWeight m k - g k / Z =
        (WalkTails.hypergeometricWeight m k - g k) + (g k - g k / Z) := by ring
  have hdist : |Z - 1| ≤ C₂ / Real.sqrt (m : ℝ) := by
    simpa [Z, g] using hE
  have hnormCorrection :
      (∑ k ∈ Finset.range (m + 1), |g k - g k / Z|) = |Z - 1| := by
    calc
      _ = ∑ k ∈ Finset.range (m + 1), g k * |1 - 1 / Z| := by
        apply Finset.sum_congr rfl
        intro k hk
        have hg : 0 ≤ g k := by dsimp [g]; positivity
        rw [show g k - g k / Z = g k * (1 - 1 / Z) by
            field_simp [hZpos.ne'], abs_mul, abs_of_nonneg hg]
      _ = Z * |1 - 1 / Z| := by rw [← Finset.sum_mul]
      _ = |Z - 1| := by
        calc
          _ = |Z| * |1 - 1 / Z| := by rw [abs_of_pos hZpos]
          _ = |Z * (1 - 1 / Z)| := by rw [abs_mul]
          _ = |Z - 1| := by congr 1; field_simp [hZpos.ne']
  have htriangle :
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k - g k / Z|) ≤
        (∑ k ∈ Finset.range (m + 1),
          |WalkTails.hypergeometricWeight m k - g k|) +
          (∑ k ∈ Finset.range (m + 1), |g k - g k / Z|) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (m + 1),
          (|WalkTails.hypergeometricWeight m k - g k| + |g k - g k / Z|) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [hnormalized k]
            exact abs_add_le _ _
      _ = _ := by rw [Finset.sum_add_distrib]
  have hbound :
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k - g k / Z|) ≤
        C₁ / Real.sqrt (m : ℝ) + C₂ / Real.sqrt (m : ℝ) :=
    htriangle.trans (add_le_add hL (hnormCorrection.le.trans hdist))
  have hbound' :
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k - g k / Z|) ≤
        (C₁ + C₂) / Real.sqrt (m : ℝ) := by
    calc
      _ ≤ C₁ / Real.sqrt (m : ℝ) + C₂ / Real.sqrt (m : ℝ) := hbound
      _ = (C₁ + C₂) / Real.sqrt (m : ℝ) := by ring
  refine ⟨by omega, ?_, hZsum, ?_⟩
  · simpa [Z, g] using hZpos
  · simpa [Z, g] using hbound'

end Critical2DKPZ.SHF.Moments
end
