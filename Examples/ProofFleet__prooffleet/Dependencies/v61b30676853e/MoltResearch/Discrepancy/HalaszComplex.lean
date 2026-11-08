import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.HalaszCapstone
/-!
# Track C: the Halász chain over ℂ (Track R, A.2 leg, A2-0)

The complex-valued mirror of the §3 Riesz/plain-sum Halász chain.  The
analytic layer (`HalaszTriple.lean`, `HalaszTripleG.lean`) is complex
end-to-end already; what needs mirroring is the ℝ-valued combinatorial
§3 chain (`tripleConvR` and its estimates) up through the capstone, so
that the plain-sum log-free Halász bound applies to the character
twists `g·χ̄` and archimedean twists `g·n^{−it}` that the [mrt]
Appendix-A mean-value layer feeds it.  Mirrors are added here as
`…C`-named copies (house rule: the 9.9k-line hosts stay untouched, new
units go in leaf files).
-/
namespace MoltResearch
namespace ExpSums
end ExpSums
end MoltResearch
