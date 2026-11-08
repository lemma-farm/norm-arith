import Examples.ProofFleet__prooffleet.Dependencies.v7d99bdc274d8.MoltResearch.Discrepancy.ZetaBound
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
/-!
# Track C: the Landau lemma substrate (Track R, campaign #3044, phase P3)

The road to the zero-free region: dividing analytic functions by their roots,
counting roots by the max-modulus principle (the Jensen-free quarter-ball
argument: roots confined to `B(s₀, R/4)` with the boundary at `R` cost a
modulus factor `≥ 3` each, so the count is `≤ M/log 3` outright), and the
Borel–Carathéodory bound on the root-free part — culminating in Landau's
inequality `-Re f'/f(s₀) ≤ C·M/R - ∑ Re 1/(s₀-ρ)`.

This file works with `ℂ → ℂ` throughout; `•` is `*`.
-/
namespace MoltResearch
namespace ExpSums
open Complex
end ExpSums
end MoltResearch
