module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.ComplexHermiteLowering
public import Mathlib
public import Mathlib.Tactic.FieldSimp
@[expose] public section
/-!
# Normalized univariate complex Hermite polynomials

For the centered complex Gaussian of precision `n`, the raw polynomial has
variance `1 / n`.  Multiplication by

`sqrt(n)^p / sqrt(p!) * (sqrt(n)^q / sqrt(q!))`

gives the paper's orthonormal normalization.  This file proves its two formal
lowering identities, including the exact coefficients `sqrt(n * p)` and
`sqrt(n * q)`.
-/
namespace GinibrePoincare
namespace ComplexHermite
end ComplexHermite
end GinibrePoincare
