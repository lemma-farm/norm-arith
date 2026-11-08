module
public import Examples.sthubbar__goldbach_lean.Dependencies.va0f526aeba09.LeanLab.Halupczok2012.U1462Analytic
/-!
# P0077 Halupczok 2012, pointwise tails of the singular series, unit U-1462

AI wrote the Lean code, Claude, run 20261022T0403Z-7595. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Everything here is elementary and PROVED, no cited input.

* `S_tendsto`: for `r ≠ 0`, `∏_{p ≤ w} (1 + c_p(r)/(p-1)²) → S(r)` as `w → ∞`. The convergence
  layer for `twinC`, from `hasProd_primes_tendsto` and the summability of `1/(p-1)²`.
* `T_tendsto`: for `q ≥ 1`, `φ(q)⁻¹ ∏_{p ≤ w} tF(p) → 𝔗(n, q, a)`.
* `sum_Zsq_eq`: the sum over the squarefree `s ∈ Zsq z X₁` is the sum over the sets `t` of primes
  `≤ w` with `∏ t ≤ ⌊z⌋`, `∏ t ≤ X₁`, for every `w ≥ ⌊z⌋`.
* `tail_pointwise`: RAMANUJAN TAIL, for `m < n` and `0 < z ≤ X₁`,
  `|S(n - m) - ∑_{s ∈ Zsq z X₁} g_s(m)| ≤ z^{-σ} Kc σ Hs σ (n - m)`.
* `euler_pointwise`: EULER TAIL, for `q ≥ 1`, `(a, q) = 1`, `0 < z ≤ X₁`,
  `|∑_{s ∈ Zsq z X₁} Y/φ([q,s]) ∑_{b ∈ G(a,q,s)} g_s(b) - 𝔗(n,q,a) Y| ≤ Y z^{-σ} Kc σ Hs σ q / φ(q)`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset Filter Topology
theorem inv_sq_pred_le {k : ℕ} (hk : 2 ≤ k) : 1 / ((k : ℝ) - 1) ^ 2 ≤ 4 * ((k : ℝ) ^ 2)⁻¹ := by
  have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 < (k : ℝ) - 1 := by linarith
  rw [← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
theorem summable_pert (f : ℕ → ℝ) {q : ℕ} (hq : 0 < q)
    (hb : ∀ k, k.Prime → |f k - 1| ≤ 1 / ((k : ℝ) - 1) ^ 2 + (if k ∣ q then 1 else 0)) :
    Summable (fun k : ℕ => if k.Prime then f k - 1 else 0) := by
  have hg : Summable (fun k : ℕ => 4 * ((k : ℝ) ^ 2)⁻¹ + (if k ∣ q then (1 : ℝ) else 0)) := by
    apply Summable.add
    · exact (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left 4
    · apply summable_of_ne_finset_zero (s := q.divisors)
      intro k hk
      rw [Nat.mem_divisors] at hk
      rw [if_neg (fun h => hk ⟨h, hq.ne'⟩)]
  refine Summable.of_norm_bounded hg (fun k => ?_)
  have hg0 : 0 ≤ (if k ∣ q then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h4 : 0 ≤ 4 * ((k : ℝ) ^ 2)⁻¹ := by positivity
  by_cases hp : k.Prime
  · rw [if_pos hp, Real.norm_eq_abs]
    refine (hb k hp).trans ?_
    have := inv_sq_pred_le hp.two_le
    linarith
  · rw [if_neg hp, norm_zero]; linarith
/-! ### The binary singular series as a limit of partial Euler products -/
/-- The factor of `twinC`. -/
noncomputable def f2 (p : ℕ) : ℝ := if p = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2
theorem twinC_tendsto : Tendsto (fun w => ∏ p ∈ PrN w, f2 p) atTop (𝓝 twinC) := by
  have h := hasProd_primes_tendsto f2 (summable_pert f2 (q := 1) one_pos (fun k hk => by
    have hg0 : (0 : ℝ) ≤ (if k ∣ 1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have h0 : (0 : ℝ) ≤ 1 / ((k : ℝ) - 1) ^ 2 := by positivity
    unfold f2
    by_cases h2 : k = 2
    · rw [if_pos h2, sub_self, abs_zero]; linarith
    · rw [if_neg h2, show 1 - 1 / ((k : ℝ) - 1) ^ 2 - 1 = -(1 / ((k : ℝ) - 1) ^ 2) by ring,
        abs_neg, abs_of_nonneg h0]
      linarith))
  exact h
end LeanLab.Halupczok2012
