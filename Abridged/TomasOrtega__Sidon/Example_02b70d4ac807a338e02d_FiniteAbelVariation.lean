module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Intervals

-- ==== Examples.TomasOrtega__Sidon.Examples.Example_02b70d4ac807a338e02d_FiniteAbelVariation ====
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.FiniteAbelVariation
noncomputable section
open scoped Classical

set_option linter.unusedVariables false in
theorem weighted_bound (w z : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hB : ∀ n ≤ N, ‖∑ k ∈ Finset.range (n + 1), z k‖ ≤ B) 
    (h_RiemannGaussian_FiniteAbelVariation_weighted_sum_eq : ∀ (w z : ℕ → ℂ) (N : ℕ),
      ∑ n ∈ Finset.range (N + 1), w n * z n =
        w N * ∑ n ∈ Finset.range (N + 1), z n +
          ∑ n ∈ Finset.range N, (w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), z k)
    :
    ‖∑ n ∈ Finset.range (N + 1), w n * z n‖ ≤
      B * (‖w N‖ + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖) := by
  rw [h_RiemannGaussian_FiniteAbelVariation_weighted_sum_eq]
  calc
    _ ≤ ‖w N * (∑ n ∈ Finset.range (N + 1), z n)‖ +
        ‖∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ k ∈ Finset.range (n + 1), z k)‖ := norm_add_le _ _
    _ ≤ ‖w N‖ * B + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB n (by have := Finset.mem_range.mp hn; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring
end
end RiemannGaussian.FiniteAbelVariation
