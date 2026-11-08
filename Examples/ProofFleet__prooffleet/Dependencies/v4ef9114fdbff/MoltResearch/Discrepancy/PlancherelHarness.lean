import Examples.ProofFleet__prooffleet.Dependencies.v4ef9114fdbff.MoltResearch.Discrepancy.ZeroFreeRegion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.RealDeriv
/-!
# Track C: the Plancherel harness (Track R, campaign #3044, phase C2)

The L² identity at the heart of the "cheap" Matomäki–Radziwiłł frame
(Tao, 254A Supplement 6): for a smooth compactly supported `F` and a
finite family of weighted translates,
`∫ ‖∑ᵢ wᵢ·F(y − sᵢ)‖² dy = ∫ ‖∑ᵢ wᵢ·e(−sᵢξ)‖²·‖𝓕F(ξ)‖² dξ` —
Plancherel plus translation↔modulation, with no measure convolution:
the prime measure `μ = ∑ (1/p)·δ_{log p}` is finitely supported, so its
convolution with `F` is literally this translate sum, and `μ̂` is the
phase sum on the right.

Everything runs in the Schwartz layer: `F` smooth compactly supported
makes the translate sum a Schwartz function, and
`SchwartzMap.integral_norm_sq_fourier` is Plancherel in integral form.
-/
namespace MoltResearch
namespace ExpSums
open Real MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform ContDiff
end ExpSums
end MoltResearch
