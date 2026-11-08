import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.PlancherelHarness
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.MultiplicativeC
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.PretentiousDist
/-!
# Track C: the Halász triple convolution, frequency side (Track R, M0R)

The log-free Halász route (GHS, "A more intuitive proof of a sharp
version of Halász's theorem"): the Riesz triple convolution of
`SmoothRankin` is paired against the exact Riesz window, with the inner
index extended from `Icc 1 x` to a countable family so that the phase
polynomial becomes the truncated Euler product `F_x` rather than a
partial sum.  This module holds the frequency-side bricks.

`tsum_translates_eq_integral_char` is the countable-family form of the
character-pairing identity `sum_translates_eq_integral_char'`: for an
absolutely summable weight family and a bounded window with Fourier
inversion,

  `∑'ₙ wₙ·F(y − sₙ) = ∫_ℝ e(ξy)·(∑'ₙ wₙ·e(−sₙξ))·𝓕F(ξ) dξ`.

The point of the extension: on the time side the extra terms are killed
by the window's support, so the identity is free — but on the frequency
side the phase sum becomes an *infinite* Dirichlet series, which for a
completely multiplicative weight family factors as an Euler product.
That factorisation is what the smooth-restriction route (`bandSup_*`,
`rankin_*`) paid a three-scale loss to approximate, and here costs
nothing.
-/
namespace MoltResearch
namespace ExpSums
open Real MeasureTheory Filter
open scoped FourierTransform
end ExpSums
end MoltResearch
