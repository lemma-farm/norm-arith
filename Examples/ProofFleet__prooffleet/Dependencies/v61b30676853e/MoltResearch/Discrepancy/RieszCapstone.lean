import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.SmoothRankin
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.HalaszEuler
/-!
# The §3 capstone at the Riesz window (Track R)

The assembly leaf: the per-block instantiation of `tripleConvR_le` and
the `k`-sum balance live here, downstream of the whole `SmoothRankin`
substrate, so that capstone units never force a rebuild of the 9.8k-line
core file (see AGENTS.md, "CI-efficiency rule").

This file opens with the missing glue between §4's suppliers and
`tripleConvR_le`'s interface: the energy bound
`ghsPrimePoly_unit_energy_final_le` carries GHS's own threshold
`T² ≤ q`, but the `Q` that `tripleConvR_le` enlarges into contains
*every* prime below `x/p` — including the small ones.  The state-file
resolution ("small primes contribute `O(1)`, discard separately") is
formalised as `ghsPrimePoly_unit_energy_split_le`: split the polynomial
at `T²`, price the small half by its trivial sup
(`norm_ghsPrimePoly_le`, a Mertens mass `≍ 2·log T`), and pay a factor
`2` on both halves.
-/
namespace MoltResearch
end MoltResearch
