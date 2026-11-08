import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.CMOfPrimes
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.PretentiousDist
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.GoodResidues
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.CharTwistCompose
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.CharTwistedSingularSeries
import Mathlib.Data.Nat.Factorization.Induction
/-!
# Discrepancy: the pretentious factorization `g = χ̃ · n^{i𝐭} · h` (Tao 2015 §4)

Language-layer module for the generalized Borwein–Choi–Coons analysis of Tao 2015
(arXiv:1509.05363, §4; issue #2871).  The pretense bound (paper eq. `(gh)`) says a
completely multiplicative unimodular sample `g` pretends to be the character twist
`n ↦ χ(n)·n^{i𝐭}`; §4 formalises this with the factorisation (paper eq. `(dos)`)

`g(n) = χ̃(n) · n^{i𝐭} · h(n)`,

where both factors are the completely multiplicative unimodular extensions
(`cmOfPrimes`) of the prime data

* `χ̃(p) = χ(p)` for `p ∤ q` and `χ̃(p) = g(p)·p^{−i𝐭}` for `p ∣ q` (`chiTilde`), and
* `h(p) = g(p)·conj(χ(p))·p^{−i𝐭}` for `p ∤ q` and `h(p) = 1` for `p ∣ q` (`hPart`).

Contents:

* `CompletelyMultiplicativeC.eq_prod_factorization` /
  `CompletelyMultiplicativeC.eq_of_forall_prime` — a guarded completely multiplicative
  sequence with value `1` at `1` is determined by its prime values (via
  `Nat.multiplicative_factorization`); the substrate for every identity below.
* `chiTilde`, `hPart` and their basic API (completely multiplicative, value `1` at `1`,
  prime evaluation, unimodularity given `Unimodular g`).
* `chiTilde_mul_cpow_mul_hPart` — the factorisation identity `(dos)` itself, checked at
  primes and propagated by complete multiplicativity.
* `pretentiousDistSq_hPart_le` — the pretense transfer `(gh) ⇒ (gap)`: the distance from
  `h` to the constant `1` is at most the distance from `g` to the twist
  `charTwist q χ 𝐭`, prime by prime.
* `hPart_eq_one_of_primes_dvd` — `h ≡ 1` on `q`-smooth numbers (used for the principal
  character in the equidistribution step).
* `chiTilde_apply_of_coprime` and `chiTilde_congr_of_good` — the χ̃-rigidity chain: on a
  good residue class `a (q^k)` (`IsGoodResidue`), the value `χ̃(n+m)` for
  `n ≡ a (q^k)` and `1 ≤ m ≤ 2H` depends only on `a + m`, via the paper's gcd splitting
  `χ̃(n+m) = χ̃((a+m, q^k)) · χ((n+m)/(a+m, q^k))` and periodicity of `χ`.

Conventions: the archimedean factor `p^{−i𝐭}` is spelled
`(p : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))` so that `norm_natCast_cpow_I_mul` and
`conj_natCast_cpow_I_mul` apply verbatim; junk values follow Mathlib (`(0:ℂ)^s = 0` for
`s ≠ 0`, `cmOfPrimes F 0 = 1`), and all identities carry the `n ≠ 0` guards of the
guarded `CompletelyMultiplicativeC`.
-/
namespace MoltResearch
/-! ### Completely multiplicative sequences are determined by their prime values -/
namespace CompletelyMultiplicativeC
variable {g h : ℕ → ℂ}
end CompletelyMultiplicativeC
/-! ### The archimedean factor `n ↦ n^{s}` -/
variable {g : ℕ → ℂ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ}
end MoltResearch
