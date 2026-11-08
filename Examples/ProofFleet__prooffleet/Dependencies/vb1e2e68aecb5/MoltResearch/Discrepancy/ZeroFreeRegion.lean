import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.LandauLemma
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
/-!
# Track C: the zero-free region substrate (Track R, campaign #3044, phase P4)

The `ζ'/ζ` legs of the zero-free region: the 3-4-1 positivity (the classical
`3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` amplification, through the von Mangoldt
L-series), and the pole bound `-ζ'/ζ(σ) ≤ 1/(σ-1) + c` on `(1, 2]` by the
compactness route (the ε-form interfaces permit nonconstructive constants, so
continuity of `-ζ'/ζ - 1/(σ-1)` up to `σ = 1` plus compactness of `[1,2]`
replaces Chebyshev partial summation entirely).

Together with `landau_inequality` and `zeta_strip_bound` these are the only
inputs of the region (P6); the Perron machinery is needed only by the later
prime-sum legs, not here.
-/
namespace MoltResearch
namespace ExpSums
open Complex
end ExpSums
end MoltResearch
