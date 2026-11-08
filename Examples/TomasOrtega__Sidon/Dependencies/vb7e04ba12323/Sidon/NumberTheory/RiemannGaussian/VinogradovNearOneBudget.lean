module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovDyadic
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovLongBlocks
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaDyadicTruncation
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLineBudget
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.VinogradovNearOneBudget
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.VinogradovScaleSelection
def delta (n : ℕ) : ℝ := 1 / (65536 * (2 * (n : ℝ) + 1) ^ 2)
def line (n : ℕ) : ℝ := 1 - delta n
def growth (n : ℕ) : ℝ := 2 * delta n / (n : ℝ)
theorem delta_pos (n : ℕ) : 0 < delta n := by unfold delta; positivity
theorem delta_le (n : ℕ) : delta n ≤ 1 / 4096 := by
  have h : (0 : ℝ) ≤ n := by positivity
  unfold delta
  apply (div_le_iff₀ (by positivity : 0 < 65536 * (2 * (n : ℝ) + 1) ^ 2)).mpr
  nlinarith [sq_nonneg (2 * (n : ℝ))]
theorem line_bounds (n : ℕ) : 1 / 2 ≤ line n ∧ line n < 1 := by
  have h := delta_le n
  have h' := delta_pos n
  unfold line
  constructor <;> linarith
theorem growth_pos {n : ℕ} (hn : 1 ≤ n) : 0 < growth n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold growth
  exact div_pos (mul_pos (by norm_num) (delta_pos n)) hn'
end
end RiemannGaussian.VinogradovNearOneBudget
