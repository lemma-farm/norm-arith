import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.PretentiousDist
/-!
# Discrepancy: composing two character twists into one composite twist

Support for the `𝐭`-cutting lemma of Tao 2015 (arXiv:1509.05363, §4, proof of the generalized
Borwein–Choi–Coons theorem). There, two applications of Proposition 1.11 produce twists
`n ↦ χ(n)·n^{i𝐭}` and `n ↦ χ'(n)·n^{i𝐭'}` both pretending to be the multiplicative function,
and "applying the pretentious triangle inequality, we conclude that

`∑_{p ≤ X^δ} (1 − Re χ(p) conj(χ'(p)) p^{−i(𝐭'−𝐭)})/p ≪_ε 1`."

The left-hand side is `pretentiousDistSq (charTwist q χ 𝐭) (charTwist q' χ' 𝐭')`, but the
Vinogradov–Korobov interface (Track C Stage 5) consumes bounds of the shape
`M ≤ pretentiousDistSq (fun _ => 1) (charTwist Q χ'' s) N` for an honest Dirichlet character
`χ''`. This module supplies the bridge (`pretentiousDistSq_one_charTwist_mul`): the distance
between the two twists **equals** the distance from the constant `1` to the single composite
twist at modulus `Q = q·q'`, character `χ'' = changeLevel χ · (changeLevel χ')⁻¹`, and
frequency `s = 𝐭 − 𝐭'` (the paper's `p^{−i(𝐭'−𝐭)} = p^{i(𝐭−𝐭')}`).

The per-prime content is `charTwist_mul_conj_charTwist`: for `0 < n`,

`χ''(n)·n^{i(t−t')} = (χ(n)·n^{it}) · conj(χ'(n)·n^{it'})`,

split into a character part (`changeLevel_mul_changeLevel_inv_apply_natCast`; the inverse of a
`ℂ`-valued Dirichlet character is its pointwise conjugate since values on units have norm one,
and off the common coprime locus both sides vanish) and an archimedean part
(`natCast_cpow_mul_conj_cpow`: `n^{it}·conj(n^{it'}) = n^{i(t−t')}`).

Also included: `natCast_mul_le_mul`, the trivial composite-modulus bound `q·q' ≤ Q·Q'` feeding
the interface's `(q : ℝ) ≤ Q` quantifier.
-/
namespace MoltResearch
end MoltResearch
