import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.LFunctionBounds
import Mathlib.NumberTheory.EulerProduct.ExpLog
/-!
# Discrepancy: the character-twisted singular series is subexponentially small

Nucleus-track module for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871, PR E2): the **non-principal character sum
bound**.  For a non-principal Dirichlet character `χ mod N` and a completely multiplicative
unimodular `h` that pretends to be `1` at scale `X`
(`pretentiousDistSq h 1 (⌊X⌋₊+1) ≤ B₀`), the `χ`-twisted singular series

`𝔖_χ = ∑'_n χ(n)·h(n)/n^{1+1/log X}`

satisfies `‖𝔖_χ‖ ≤ C(χ)·exp(√(2B₀)·√(4·log log X + 17))` — subexponentially small compared
to the `≍ log X` size of the untwisted series (paper §4, the displayed chain for the
non-principal characters ending in `≪_{q,k} exp(O_ε((log log X)^{1/2}))`; our crude
constants land `√(4·log log X + 17)` in place of the paper's `O_ε((log log X)^{1/2})`).

Proof architecture (all constants crude and explicit, mirroring
`exp_neg_mul_log_le_norm_zetaWeightedSum` and `exists_re_tsum_primes_char_le`):
- Euler product: `‖𝔖_χ‖ = exp(Re T)` with `T = ∑'_p −log(1 − χ(p)h(p)/p^σ)`, and `T`
  linearizes to the prime sum `F = ∑'_p χ(p)h(p)/p^σ` up to `1`
  (`norm_tsum_neg_log_euler_sub_le`).
- Split `χ(p)h(p) = χ(p) + χ(p)(h(p) − 1)` per prime: the pure character sum has
  `Re ≤ C'` uniformly in `X ≥ 3` (`exists_re_tsum_primes_char_le`, the analytic
  `L(s, χ)`-continuation input); the correction is `≤ ∑'_p ‖h(p) − 1‖/p^σ` in norm.
- The correction below scale `X` is controlled by **Cauchy–Schwarz**
  (`∑_{p<X} ‖h(p)−1‖/p ≤ √(∑ ‖h(p)−1‖²/p)·√(∑ 1/p)`), with the circle identity
  `‖z − 1‖² = 2(1 − Re z)` converting the first factor into `√(2·𝔻²) ≤ √(2B₀)` and the
  crude Mertens bound `sum_primesBelow_one_div_le` giving the second factor
  `√(4·log log X + 17)`; the Chebyshev tail (`sum_primes_Ioc_one_div_rpow_le`) handles
  primes above `X` (contribution `≤ 16`).
-/
namespace MoltResearch
open Finset
/-- The pointwise product of two guarded completely multiplicative sequences is guarded
completely multiplicative (the `a ≠ 0`, `b ≠ 0` guards transfer verbatim). -/
theorem CompletelyMultiplicativeC.mul {g₁ g₂ : ℕ → ℂ} (hg₁ : CompletelyMultiplicativeC g₁)
    (hg₂ : CompletelyMultiplicativeC g₂) :
    CompletelyMultiplicativeC fun n => g₁ n * g₂ n := by
  intro a b ha hb
  dsimp only
  rw [hg₁ a b ha hb, hg₂ a b ha hb]
  ring
end MoltResearch
