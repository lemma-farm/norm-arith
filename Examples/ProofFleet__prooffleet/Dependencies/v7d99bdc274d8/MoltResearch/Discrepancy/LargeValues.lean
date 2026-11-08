import Examples.ProofFleet__prooffleet.Dependencies.v7d99bdc274d8.MoltResearch.Discrepancy.PlancherelHarness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Track C: large values of prime-block phase sums (Track R, C4a)

The kernel toolkit for the C4a window-energy bound: the oscillation kernel
`‖∫_{-L}^{L} e(−sξ) dξ‖ ≤ 1/(π|s|)`, the phase-product law
`e(−uξ)·conj(e(−vξ)) = e(−((u−v)ξ))`, the interval real-part commute, and
the log-separation `log q − log p ≥ (q−p)/q`.

The window-energy expansion (next unit) combines these with the
reciprocal prime-gap sum of `BrunTitchmarsh.lean`: the energy of
`S(ξ) = ∑_{p∈P} (a_p/p)·e(−ξ·log p)` over `[−L, L]` is at most
`2L·∑ 1/p² + (∑ 1/p)·O(loglog P₊)`, which caps the number of
`1`-separated `δE`-large values at `O_δ(1)` — the first leg of the C4
dichotomy.
-/
namespace MoltResearch
namespace ExpSums
open Real MeasureTheory
end ExpSums
end MoltResearch
