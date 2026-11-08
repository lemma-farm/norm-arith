import Examples.ProofFleet__prooffleet.Dependencies.v08927546f6f6.MoltResearch.Discrepancy.MultiplicativeC
/-!
# Discrepancy: log-averaged two-point correlation

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the log-averaged two-point correlation that the logarithmically averaged Elliott interface
(arXiv:1509.05422, Thm 1.3) is stated about:

`logAvgCorr g a b N = (∑ n ∈ Icc 1 N, g (n + a) * conj (g (n + b)) / n) / log N`.

Conventions (from the card's decision record):
- division is ℂ-division throughout (`/ (n : ℂ)`, never `Nat` division);
- `Real.log N` junk values at `N ≤ 1` are embraced, not fought: `Real.log 0 = Real.log 1 = 0`
  and ℂ-division by `0` is `0`, so `logAvgCorr g a b N = 0` for `N ≤ 1` — normalized by the
  simp lemmas below.

Degenerate-parameter simp lemmas:
- `logAvgCorr_zero_N` / `logAvgCorr_one_N` — the `N ≤ 1` junk values are `0`.
- `Unimodular.logAvgCorr_self` — the diagonal `a = b` value for unimodular `g` collapses to the
  log-averaged harmonic sum `(∑ n ∈ Icc 1 N, (n : ℂ)⁻¹) / log N` (each correlation term is `1`).
-/
namespace MoltResearch
namespace Unimodular
variable {g : ℕ → ℂ}
end Unimodular
end MoltResearch
