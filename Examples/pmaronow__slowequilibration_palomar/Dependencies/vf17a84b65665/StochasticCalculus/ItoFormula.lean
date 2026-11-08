/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.StochasticCalculus.QuadraticVariationDensity
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
set_option autoImplicit false
@[expose] public section
/-!
# Taylor partition sums along Brownian paths

The pieces of the Itô-formula development that the pricing chain uses: the
Taylor remainder of a twice differentiable function, its uniform bounds on
compact intervals, and the convergence along uniform partitions of the
derivative-weighted increment sums, the left Riemann sums, and the
quadratic-variation-controlled remainder sums.
-/
public section
open MeasureTheory Set
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
variable {W : Type*}   [MeasurableSpace W]
  {P : Measure W} {B : ℝ≥0 → W → ℝ}
namespace StochasticCalculus
/-- The remainder after subtracting the explicit second-order Taylor polynomial. -/
@[expose] noncomputable def itoTaylorRemainder (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  f x - (f x₀ + deriv f x₀ * (x - x₀) +
    (1 / 2 : ℝ) * deriv (deriv f) x₀ * (x - x₀) ^ 2)
/-- The second iterated derivative is the ordinary second derivative. -/
private lemma iteratedDeriv_two (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
    show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
/-- The remainder after subtracting the first-order Taylor polynomial. -/
private noncomputable def itoFirstTaylorRemainder
    (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  f x - (f x₀ + deriv f x₀ * (x - x₀))
/-- Abstract endpoint for the Taylor-remainder step: termwise little-o
coefficients times an eventually bounded quadratic sum have vanishing total
remainder. -/
private theorem tendsto_sum_zero_of_remainder_bound
    {N : ℕ → ℕ} {r Δ : ℕ → ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      ∑ i ∈ Finset.range (N n), (Δ n i) ^ 2 ≤ C)
    (hremainder : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ i ∈ Finset.range (N n),
        |r n i| ≤ ε * (Δ n i) ^ 2) :
    Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range (N n), r n i)
      Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  let δ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  rcases (Filter.eventually_atTop.1 hquadratic) with ⟨nq, hnq⟩
  rcases (Filter.eventually_atTop.1 (hremainder δ hδ)) with ⟨nr, hnr⟩
  refine ⟨max nq nr, fun n hn ↦ ?_⟩
  have hq := hnq n (le_trans (le_max_left _ _) hn)
  have hr := hnr n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, sub_zero]
  calc
    |∑ i ∈ Finset.range (N n), r n i| ≤
        ∑ i ∈ Finset.range (N n), |r n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (N n), δ * (Δ n i) ^ 2 := by
      exact Finset.sum_le_sum fun i hi ↦ hr i hi
    _ = δ * ∑ i ∈ Finset.range (N n), (Δ n i) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hq hδ.le
    _ = ε / 2 := by
      dsimp only [δ]
      field_simp [ne_of_gt hC]
    _ < ε := by linarith
/-- Every partition point with index at most the denominator lies in `[0, t]`. -/
private lemma uniformPartitionTime_mem_Icc
    (t : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    uniformPartitionTime t n i ∈ Icc 0 t := by
  constructor
  · exact bot_le
  · unfold uniformPartitionTime
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    calc
      t * (i : ℝ≥0) / (n : ℝ≥0) ≤ t * (n : ℝ≥0) / (n : ℝ≥0) := by
        gcongr
      _ = t := mul_div_cancel_right₀ t hn0
/-- Adjacent uniform partition points are exactly one mesh width apart. -/
private lemma dist_uniformPartitionTime_succ
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    dist (uniformPartitionTime t n (i + 1)) (uniformPartitionTime t n i) =
      ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
  have hle : uniformPartitionTime t n i ≤ uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  rw [NNReal.dist_eq, abs_of_nonneg]
  · simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_natCast]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnR]
    norm_num [Nat.cast_add, Nat.cast_one]
  · exact sub_nonneg.mpr (by exact_mod_cast hle)
/-- A continuous path has uniformly vanishing increments along the project's
uniform partitions. -/
private theorem continuous_uniformPartition_increments
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |g (uniformPartitionTime t (n + 1) (i + 1)) -
          g (uniformPartitionTime t (n + 1) i)| < δ := by
  have huc : UniformContinuousOn g (Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  intro δ hδ
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  have hdivNN : Filter.Tendsto
      (fun n : ℕ ↦ t / ((n + 1 : ℕ) : ℝ≥0)) Filter.atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun n : ℕ ↦ ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (𝓝 0) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun n : ℕ ↦ t / ((n + 1 : ℕ) : ℝ≥0))
      Filter.atTop (𝓝 (0 : ℝ))
    simpa only [NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv η hη
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro i hi
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi' : i ≤ n + 1 := le_trans (Nat.le_add_right i 1) hipos
  have hx := uniformPartitionTime_mem_Icc t hnpos hi'
  have hy := uniformPartitionTime_mem_Icc t hnpos hipos
  have hmesh : ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < η := by
    have := hN n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] using this
  have hdist :
      dist (uniformPartitionTime t (n + 1) (i + 1))
        (uniformPartitionTime t (n + 1) i) < η := by
    rw [dist_uniformPartitionTime_succ t hnpos i]
    exact hmesh
  have hout := hmod _ hy _ hx hdist
  simpa only [Real.dist_eq] using hout
/-- A continuous real-valued path on a finite time interval has its range in
a compact real interval. -/
private theorem continuous_nnreal_range_subset_Icc
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    ∃ a b : ℝ, ∀ s ∈ Icc (0 : ℝ≥0) t, g s ∈ Icc a b := by
  let K : Set ℝ := g '' Icc (0 : ℝ≥0) t
  have hK : IsCompact K := isCompact_Icc.image hg
  refine ⟨sInf K, sSup K, ?_⟩
  intro s hs
  have hgs : g s ∈ K := ⟨s, hs, rfl⟩
  exact ⟨csInf_le hK.bddBelow hgs, le_csSup hK.bddAbove hgs⟩
section CenteredWeightedQuadraticVariation
variable {Omega I E : Type*} [MeasurableSpace Omega]
end CenteredWeightedQuadraticVariation
end StochasticCalculus
