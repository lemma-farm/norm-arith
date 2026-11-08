import Examples.ProofFleet__prooffleet.Dependencies.v08927546f6f6.MoltResearch.Discrepancy.LogAvgCorr
/-!
# Discrepancy: pretentious (Granville–Soundararajan) distance, finite-`N` form

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the finite-truncation pretentious distance used to state the non-pretentiousness hypothesis of
the logarithmically averaged Elliott theorem (arXiv:1509.05422):

`𝔻(g, h; N)² = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

Conventions:
- The prime range is `Nat.primesBelow N` (primes strictly below `N`) — the Mathlib-idiomatic
  finite prime truncation; interfaces quantifying over all `N` are insensitive to `< N` vs `≤ N`.
- The **squared** distance `pretentiousDistSq` is the primary definition (the literature works
  with `𝔻²` throughout); `pretentiousDist` is its square root.
- Junk values are embraced: without unimodularity hypotheses the summands can be negative, so
  the order lemmas below carry `Unimodular` hypotheses rather than baking them into the
  definition.

Monotonicity basics (this module deliberately stops here):
- `pretentiousDistSq_summand_nonneg`, `pretentiousDistSq_nonneg` — nonnegativity for unimodular
  arguments.
- `pretentiousDistSq_mono` / `pretentiousDist_mono` — monotone in the truncation `N`.
- `Unimodular.pretentiousDistSq_self` — the diagonal vanishes (each summand is `0`).
-/
namespace MoltResearch
/-- Squared finite-`N` pretentious distance (Granville–Soundararajan):

`pretentiousDistSq g h N = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

The non-pretentiousness hypothesis of the log-Elliott interface says this tends to `∞` with `N`
for every character-modulated comparison `h`.
-/
noncomputable def pretentiousDistSq (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, (1 - (g p * (starRingEnd ℂ) (h p)).re) / p
variable {g h : ℕ → ℂ}
namespace Unimodular
end Unimodular
/-! ### Quasi-triangle inequality

The sharp Granville–Soundararajan triangle inequality for `pretentiousDist` is not needed by
the derivation-(C) bookkeeping (all its pretense bounds are `O(1)`), so we state only the
elementary squared-distance version with constant `3`, which has a pointwise proof on the
closed unit disc. -/
theorem pretentiousDistSq_le_add_mass (g h : ℕ → ℂ)
    (hg : ∀ p, ‖g p‖ ≤ 1) (hh : ∀ p, ‖h p‖ ≤ 1) {y x : ℕ} (hyx : y ≤ x) :
    pretentiousDistSq g h x
      ≤ pretentiousDistSq g h y
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
              - (∑ p ∈ y.primesBelow, (1:ℝ)/p)) := by
  classical
  have hsub : y.primesBelow ⊆ x.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  unfold pretentiousDistSq
  rw [← Finset.sum_sdiff hsub]
  have hmass : ∑ p ∈ x.primesBelow \ y.primesBelow, (1:ℝ)/(p:ℝ)
      = (∑ p ∈ x.primesBelow, (1:ℝ)/p)
        - (∑ p ∈ y.primesBelow, (1:ℝ)/p) :=
    Finset.sum_sdiff_eq_sub hsub
  have hextra : ∑ p ∈ x.primesBelow \ y.primesBelow,
      (1 - (g p * (starRingEnd ℂ) (h p)).re) / p
        ≤ ∑ p ∈ x.primesBelow \ y.primesBelow, 2*((1:ℝ)/p) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : p.Prime :=
      Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hre : |(g p * (starRingEnd ℂ) (h p)).re| ≤ 1 := by
      calc |(g p * (starRingEnd ℂ) (h p)).re|
          ≤ ‖g p * (starRingEnd ℂ) (h p)‖ := Complex.abs_re_le_norm _
        _ = ‖g p‖ * ‖h p‖ := by rw [norm_mul, RingHomIsometric.norm_map]
        _ ≤ 1 * 1 := mul_le_mul (hg p) (hh p) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h1 : 1 - (g p * (starRingEnd ℂ) (h p)).re ≤ 2 := by
      have := abs_le.mp hre
      linarith [this.1]
    rw [div_le_iff₀ hp0, mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hp0),
      mul_one]
    exact h1
  rw [← hmass, Finset.mul_sum]
  linarith [hextra]
end MoltResearch
