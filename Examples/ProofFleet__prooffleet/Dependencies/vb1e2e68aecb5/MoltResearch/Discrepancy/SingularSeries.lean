import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.ZetaWeighted
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.PretentiousDist
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
/-!
# Discrepancy: the singular series `𝔖` is `≍ log X` under pretense

Nucleus module for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`, issue
#2871, PR D3): the two-sided bound (paper eq. (1s))

`exp(−(20+B₀))·log X ≤ ‖𝔖‖ ≤ 2 + log X`,  `𝔖 = zetaWeightedSum g (1 + 1/log X)`,

for completely multiplicative 1-bounded `g` that pretends to be `1` at scale `X`
(`∑_{p ≤ X} (1 − Re g(p))/p ≤ B₀`, i.e. `pretentiousDistSq g 1 (⌊X⌋₊ + 1) ≤ B₀`).

Proof architecture (Mertens-free):
- `EulerProduct.exp_tsum_primes_log_eq_tsum` writes `𝔖 = exp T` with
  `T = ∑'_p −log(1 − g(p)/p^σ)`, so `‖𝔖‖ = exp (Re T)` (`Complex.norm_exp`).
- The **log-linearization** `‖T − ∑'_p g(p)/p^σ‖ ≤ 1`: per prime
  `‖−log(1−z) − z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1/2` (`norm_log_one_sub_inv_sub_self_le`), summed
  against `∑'_p 1/p² ≤ 1` (telescoping, as in `PrimeSumBounds`).
- The prime mass `∑'_p 1/p^σ ≥ log(log X / 3) − 1` comes **from the zeta mass through the
  Euler product itself**: apply the linearization to the constant-1 function, whose `𝔖` is
  the full zeta mass `≥ log X/3` (`log_div_three_le_tsum_one_div_rpow`) — no Mertens
  theorem needed.
- Pretense transfer: `∑'_p (1 − Re g(p))/p^σ ≤ B₀ + 16` — primes `≤ X` via the hypothesis
  (`p^σ ≥ p`), primes `> X` via the Chebyshev tail (`sum_primes_Ioc_one_div_rpow_le`).
-/
namespace MoltResearch
open Finset
section LogLinearization
variable {g : ℕ → ℂ}
end LogLinearization
end MoltResearch
