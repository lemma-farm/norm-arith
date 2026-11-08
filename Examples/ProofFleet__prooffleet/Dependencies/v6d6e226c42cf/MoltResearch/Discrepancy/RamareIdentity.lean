import Examples.ProofFleet__prooffleet.Dependencies.v6d6e226c42cf.MoltResearch.Discrepancy.TuranKubilius
import Examples.ProofFleet__prooffleet.Dependencies.v6d6e226c42cf.MoltResearch.Discrepancy.LargeValues
import Examples.ProofFleet__prooffleet.Dependencies.v6d6e226c42cf.MoltResearch.Discrepancy.DyadicMVT
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
/-!
# Track C: the Ramaré double-count identity (Track R, C4e-1)

The exact combinatorial engine of the `𝒰`-decomposition: for any finsets
`A, P` and weight `g`,

  `∑_{p∈P} ∑_{n∈A, p∣n} g(n)/ω_P(n) = ∑_{n∈A, ω_P(n)≥1} g(n)`,

where `ω_P(n) = #{p ∈ P : p ∣ n}`. Each `n` with `ω_P(n) = k ≥ 1` lies
in exactly `k` fibres, each weighted `1/k`. This is the identity behind
the `[MR]`-style factorization `F = ∑_p f(p)p^{−s}·G_p + (collision
terms)`: the C4e assembly splits `n = p·m` in each fibre and pushes the
`p ∤ m` main terms through the dyadic MVT (`DyadicMVT.lean`) while the
`p² ∣ n` collisions are second order.

Same swap pattern as the Turán–Kubilius first moment
(`sum_card_dvd_div_eq`); no primality enters.
-/
open Finset
namespace MoltResearch
end MoltResearch
