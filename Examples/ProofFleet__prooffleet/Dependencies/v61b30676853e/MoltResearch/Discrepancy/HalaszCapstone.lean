import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.RieszCapstone
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.HalaszTripleG
/-!
# Track C: the Riesz capstone through the smooth tsum (Track R, M0R-5)

The capstone chain of `RieszCapstone.lean`, rewired through
`tripleConvR_le'`: the per-block sharp estimate with the band sup
demanded of the smooth phase sum — the truncated Euler product — rather
than the finite `ghsMainPoly`.  The `b`-parametric assembly
`rieszMean_log_le_of_nonPretentious` already exists at the full Riesz
mean; this file rebuilds its per-block input so that `b` can be
instantiated log-freely by `norm_smoothPhaseSum_le_of_nonPretentious`,
with the tail priced at the smooth mass (`smooth_mass_le`) instead of
the harmonic sum over `Icc 1 x`.
-/
namespace MoltResearch
end MoltResearch
