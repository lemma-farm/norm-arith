import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.SmoothRankin
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.HalaszTriple
/-!
# Track C: the §4 pairing chain at an abstract main factor (Track R, M0R-4)

The GHS §4 pairing estimate, re-plumbed so the main factor need not be
a finite Dirichlet polynomial (campaign #3044, M0R-4a).

`pairing_halasz_sqrt_le` is already abstract in its three factors; what
ties the assembled chain (`ghs_pairing_estimate` and its descendants)
to `ghsMainPoly f S` — a *finite* partial sum — is only the discharge
of its side conditions:

* the integrability package uses `continuous_ghsMainPoly`, and
* the tail estimate prices the main factor at its trivial sup
  `norm_ghsMainPoly_le = ∑_{n ∈ S} 1/n`.

Both uses are parametric in nothing but *continuity* and a *global
bound*.  This file re-states the two side-condition lemmas for an
abstract main factor `G : ℝ → ℂ` with hypotheses `Continuous G` and
`∀ ξ, ‖G ξ‖ ≤ Gmax` — the shape the `x`-smooth phase *tsum* (the
truncated Euler product `F_x(1 + 2πiξ)` of `HalaszTriple`) satisfies
with `Gmax` the smooth mass `∑'_{n x-smooth} 1/n`.

That swap is the point of the M0R campaign: the band sup of the smooth
tsum is `e⁵·(2+log x)·e^{−A}` by
`norm_phase_euler_prod_le_of_nonPretentious`, log-free at a single
scale, where the finite polynomial's band sup could only be reached
through the lossy smooth-restriction detour.
-/
namespace MoltResearch
namespace ExpSums
open Real MeasureTheory Filter
open scoped FourierTransform
end ExpSums
end MoltResearch
