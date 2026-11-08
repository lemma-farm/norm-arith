import Mathlib
/-!
# The band schedule (Track R, `[mrt]` A.2, §4)

The `[mrt]` A.2 inner-band estimate is assembled from legs that each produce an
explicit real bound; `MoltResearch.Discrepancy.BandCapstone` composes them.  What
remains after that composition is *numerical*: each leg's bound must be shown to
fit inside its share of the band's slice budget

  `𝔅 = c₃ ε² (Δ/A) / 8`     (design report §4.1),

and the schedule `S1–S7` of §4.4 is exactly a choice of parameters making every
leg fit at once.  This module is that arithmetic.  It is deliberately free of
measure theory and of every in-tree dependency: each statement is an inequality
between real expressions, whose left-hand side is the *literal* right-hand side
of a merged band lemma, so a consumer composes with `le_trans` and nothing else.

**Why the conditions are hypotheses.**  §4.3 does not prove the legs fit; it
derives, leg by leg, the condition under which they do (`N_j ≥ C/ε³`,
`P₁ ≥ C/ε³`, a lower bound on `γ`, …).  Each lemma here takes that condition in
explicit form and concludes the fit.  Discharging all of them simultaneously
from a concrete `W`-schedule is a separate, self-contained computation.

## The collar leg (§4.3(a)), and one correction to the report

The report prices a collar as `e^π(T/A + 2)·Σ_{collar} 1/n ≈ 3e^π/N_j`, compares
that to `𝔅`, and reads off `N_j ≥ C/ε³` with an absolute `C`.  That is the cost
of **one** collar.  The quantity the tree actually produces — the error half of
`setIntegral_norm_sq_cell_prime_block_le` — is the assembled one, and it carries
two factors the report's estimate does not:

* the Cauchy–Schwarz factor `#I` over cells (the cell contributions are not
  orthogonal on `G`), and
* the weight `∑_v (∑_{p ∈ 𝒞_v} 1/p)²`, from the outer prime mass of each cell.

Both are exposed here as parameters rather than absorbed, because their product
is *not* absolutely bounded: `#I` grows linearly in the e-adic resolution `N`,
which cancels the `1/N` the collar ratio buys.  What saves the leg is that the
second factor is small — each `e`-adic cell has multiplicative width `e^{1/(2N)}`,
so `∑_v σ_v² ≤ (max_v σ_v)·∑_v σ_v` decays in `N` as well.  The honest condition
is therefore `N ≥ 64·#I·X·S₂/(κc₃ε³)` with `X` and `S₂` as below, not
`N ≥ C/ε³` at absolute `C`.
-/
namespace MoltResearch
/-- **The band's share of the slice budget** (Track R, A2-III, §4.1).

For the *normalised* integrand `F(ξ) = ∑ (g m/m)·e(−ξ log m)`, the prior slice
arithmetic gives the band `∫_band |F|² ≤ c₃ε²(Δ/A)/8`.  The third argument is
the ratio `ρ = Δ/A`; keeping it as one parameter is what makes the `Δ/A`
cancellation of §4.1 visible — the trivial bound carries the same factor, so the
requirement is a saving of `ε²` and nothing else. -/
noncomputable def bandBudget (c₃ ε ρ : ℝ) : ℝ := c₃ * ε ^ 2 * ρ / 8
/-- The budget is nonnegative whenever `c₃` and the ratio `ρ = Δ/A` are. -/
theorem bandBudget_nonneg (c₃ ε ρ : ℝ) (hc₃ : 0 ≤ c₃) (hρ : 0 ≤ ρ) :
    0 ≤ bandBudget c₃ ε ρ := by
  unfold bandBudget
  positivity
end MoltResearch
