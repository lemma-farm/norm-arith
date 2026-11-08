import Examples.ProofFleet__prooffleet.Dependencies.v6d6e226c42cf.MoltResearch.Discrepancy.TuranKubilius
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Discrepancy: Brun–Titchmarsh, the linear-sieve floor (Track R, C4a-0)

The `s = 0` specialization of the Track-S Selberg machinery: the sieve
polynomial `n(0−n) = −n²` sifts exactly the multiples of each prime
(`sieveRootCard_zero_prime`), so `card_sift_le_primorial_master` at `s = 0`
is the linear sieve for a plain interval. This file supplies its `G`-floor:
the squarefree harmonic floor `log z ≤ 2·∑_{k ≤ z squarefree} 1/k` (via the
`n = b²a` decomposition) gives `selbergG 0 (primorial z) z ≥ ½·log z`.

The next unit assembles these into the Brun–Titchmarsh interval bound
`#{p prime : a < p ≤ a+K} ≤ 256·K/log K`, the prime-gap-thinning input of
the C4a large-values count (campaign #3044).
-/
namespace MoltResearch
open Finset
end MoltResearch
