module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.vacbc1231f3b8.MathCollab.Density.Stronger.Fourth.Coefficients ====
public section
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See the root THIRD_PARTY_NOTICES.md (MIT-0).
No upstream project or Architect module is imported.
-/
@[expose] public section
open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
noncomputable def divisorWeight (n : ℕ) : ℂ :=
  (n.divisors.card : ℂ)

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.vacbc1231f3b8.MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixVectors ====
public section
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
@[expose] public section
/-!
# Actual alternating coefficients and height-dependent prefix vectors

Each height retains its own prefix. The exact Gram entry has the minimum
of the two prefix lengths and the same zero-based source block.
-/
set_option autoImplicit false
noncomputable section
open Complex
open MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonBlockCoefficientEnergy (m N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ‖divisorWeight (m+i)‖^2

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_5c63ac2ba847cfdef7f4_AtkinsonCoefficientEnergy ====
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
@[expose] public section
open Complex Finset Set Filter
open scoped ComplexConjugate

open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
set_option linter.unusedVariables false in
theorem exists_atkinsonBlockCoefficientEnergy_le {ε : ℝ} (hε : 0 < ε) 
    (h_MathCollab_Density_divisor_card_subpower : ∀ {η : ℝ}, 0 < η → ∃ (C : ℝ), 1 ≤ C ∧ ∀ (n : ℕ), 0 < n → (↑n.divisors.card : ℝ) ≤ C * (↑n : ℝ) ^ η)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 0 < m → N ≤ m →
      atkinsonBlockCoefficientEnergy m N ≤ C*(m:ℝ)^(1+ε) := by
  obtain ⟨D,hD1,hdiv₀⟩ := h_MathCollab_Density_divisor_card_subpower
    (show 0 < ε/2 by linarith)
  have hD : 0 < D := by linarith
  have hdiv (n : ℕ) (hn : 0 < n) : ‖divisorWeight n‖ ≤ D*(n:ℝ)^(ε/2) := by
    simpa only [divisorWeight, Complex.norm_natCast] using hdiv₀ n hn
  refine ⟨D^2*(2:ℝ)^ε,by positivity,?_⟩
  intro m N hm hN
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have h2m : (0:ℝ) < 2*(m:ℝ) := by positivity
  have hterm (i : ℕ) (hi : i ∈ Finset.range N) :
      ‖divisorWeight (m+i)‖^2 ≤ D^2*(2:ℝ)^ε*(m:ℝ)^ε := by
    have hiN := Finset.mem_range.mp hi
    have hn : 0 < m+i := by omega
    have hnR : ((m+i:ℕ):ℝ) ≤ 2*(m:ℝ) := by
      exact_mod_cast (show m+i ≤ 2*m by omega)
    have hb := (hdiv (m+i) hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnR (by linarith : 0 ≤ ε/2)) hD.le)
    apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
    rw [mul_pow,sq ((2*(m:ℝ))^(ε/2)),← Real.rpow_add h2m,
      show ε/2+ε/2 = ε by ring,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hmR.le]
    ring
  have hNR : (N:ℝ) ≤ m := by exact_mod_cast hN
  calc
    _ ≤ ∑ i ∈ Finset.range N, D^2*(2:ℝ)^ε*(m:ℝ)^ε := Finset.sum_le_sum hterm
    _ = (N:ℝ)*(D^2*(2:ℝ)^ε*(m:ℝ)^ε) := by simp
    _ ≤ (m:ℝ)*(D^2*(2:ℝ)^ε*(m:ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hNR (by positivity)
    _ = (D^2*(2:ℝ)^ε)*(m:ℝ)^(1+ε) := by
      rw [Real.rpow_add hmR,Real.rpow_one]
      ring
end MathCollab.Density.Stronger.Atkinson
