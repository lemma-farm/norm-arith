module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.Vinogradov.TernaryArcs
/-!
# The ternary major arcs: the approximation on each arc

Lab proof, unit U-5254. AI wrote this file. Known mathematics, no cited input.

* `arc_approx`: on the arc of `a/q`, `𝓕Φ(k)` is within
  `E(1 + 2πN/(q(Q + 1)))` of `μ(q)/φ(q) V(-(k/M - a/q))`, whenever the major arc
  approximation `S(a'/q + β) ≈ μ(q)/φ(q) V(β)` holds with error `E(1 + 2π|β|N)`.
* `sum_majIdx`: `∑_{(q, a) reduced, q ≤ P} g(q) = ∑_{q ≤ P} φ(q) g(q)`.
-/
@[expose] public section
namespace LeanLab.PNTPort.Vinogradov
open Complex Finset Real ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve
end LeanLab.PNTPort.Vinogradov
