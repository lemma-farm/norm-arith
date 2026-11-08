module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.LargeSieve.Dual
/-!
# The large sieve at Farey fractions

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

The reduced fractions `a/q` with `1 ≤ q ≤ Q`, `0 ≤ a < q`, `gcd(a, q) = 1` are `1/Q²`-spaced
modulo one, so

  `∑_{q ≤ Q} ∑_{a mod q, (a,q)=1} ‖∑_{M<n≤M+N} a_n e(n a/q)‖² ≤ (N + 2Q²) ∑_n ‖a_n‖²`.

This is the form used for Bombieri-Vinogradov; the sharp constant is `N - 1 + Q²`.
-/
@[expose] public section
namespace LeanLab.PNTPort.LargeSieve
open Complex Finset Real
end LeanLab.PNTPort.LargeSieve
