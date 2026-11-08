import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.LogDifferences
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Track C: the zeta tail estimate (Track L, campaign #3020)

The elementary tail bound for `∑ n^{-s}` beyond `2‖s-1‖`: each term is
telescoped against the potential `n^{1-s}/(s-1)`, with the second-order
exponential bound `‖e^z - 1 - z‖ ≤ ‖z‖²` standing in for calculus — no
integration anywhere. The partial sums of the tail are uniformly `≤ 4`,
hence so is the L-series remainder (`norm_LSeries_one_sub_partial_le`).
Together with `zeta_head_bound` this pins `‖ζ(s)‖` just right of the
`1`-line to `O(log|t|/log log|t|)` — the Littlewood-strength bound the
Vinogradov–Korobov interface reduces to.
-/
namespace MoltResearch
namespace ExpSums
open Finset
end ExpSums
end MoltResearch
