/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialIBP
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianPoincareN
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Calculus and growth for polynomial functions on `ℝⁿ`

For `p : MvPolynomial (Fin n) ℝ` the function `x ↦ eval x p` is smooth
(`contDiff_eval`), its coordinate derivative is the evaluation of the formal partial derivative
(`coordinateDerivative_eval`), and it has polynomial growth together with its derivative
(`exists_growth_eval`).  Consequently the Gaussian Poincaré inequality applies to every polynomial
(`gaussian_poincare_eval`).
-/
public section
open MvPolynomial MeasureTheory ProbabilityTheory
namespace RegularityStructures
variable {n : ℕ}
private def HasPolyBound (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : Fin n → ℝ, |g x| ≤ C * (1 + ‖x‖) ^ N
private lemma one_le_one_add_norm (x : Fin n → ℝ) : 1 ≤ 1 + ‖x‖ := by
  linarith [norm_nonneg x]
private lemma HasPolyBound.add {g h : (Fin n → ℝ) → ℝ} (hg : HasPolyBound g)
    (hh : HasPolyBound h) : HasPolyBound (fun x => g x + h x) := by
  obtain ⟨C₁, N₁, hC₁, hg⟩ := hg
  obtain ⟨C₂, N₂, hC₂, hh⟩ := hh
  refine ⟨C₁ + C₂, N₁ + N₂, by positivity, fun x => ?_⟩
  have h1 : (1 + ‖x‖) ^ N₁ ≤ (1 + ‖x‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ (one_le_one_add_norm x) (Nat.le_add_right _ _)
  have h2 : (1 + ‖x‖) ^ N₂ ≤ (1 + ‖x‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ (one_le_one_add_norm x) (Nat.le_add_left _ _)
  calc |g x + h x| ≤ |g x| + |h x| := abs_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ N₁ + C₂ * (1 + ‖x‖) ^ N₂ := add_le_add (hg x) (hh x)
    _ ≤ (C₁ + C₂) * (1 + ‖x‖) ^ (N₁ + N₂) := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 hC₁) (mul_le_mul_of_nonneg_left h2 hC₂)
private lemma HasPolyBound.sum {ι : Type*} (s : Finset ι) {g : ι → (Fin n → ℝ) → ℝ}
    (hg : ∀ i ∈ s, HasPolyBound (g i)) : HasPolyBound (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun x => by simp⟩
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
end RegularityStructures
end
