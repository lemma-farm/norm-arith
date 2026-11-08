import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.LargeValues
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.SelbergLinear
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.PlancherelHarness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
/-!
# Track C: the Parseval bridge (Track R, B-arc)

The bridge from the major-arc interface's log-averaged window target

  `∑_{n ∈ (x/w, x]} ‖W_n‖/(H·n) ≤ ε·log w`

to the frequency-side objects (`PlancherelHarness`,
`DyadicMVT`/`HalaszEuler` energies). Units: B1 the outer
Cauchy–Schwarz (this file's opener), B2 the dyadic range decomposition,
B3 the discrete-to-smoothed window comparison, B4 the per-dyadic
regime-split assembly.
-/
open Finset
namespace MoltResearch
namespace ExpSums
open scoped ContDiff
open Real MeasureTheory
open scoped FourierTransform ContDiff
end ExpSums
end MoltResearch
