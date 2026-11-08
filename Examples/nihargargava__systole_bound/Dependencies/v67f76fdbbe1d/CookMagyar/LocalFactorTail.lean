module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.SingularSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
open scoped BigOperators ComplexConjugate
namespace SystolicGrowth
namespace CookMagyarFiniteFourier
/-! # Large-prime finite-field estimates for the local cubic factor

This file starts the analytic treatment of the large-prime Euler factors.
Everything here is finite and exact.  The main ingredient is one Weyl
difference: the square of a complete cubic sum is a sum of complete
quadratic sums.  Quadratic sums are evaluated using only additive-character
orthogonality.

The final theorem gives a target-uniform `O_n(p⁻⁷)` bound for the
prime-modulus coefficient `B(T,p)`.  It deliberately does **not** identify
that coefficient with the whole local factor
`1 + ∑_{k≥1} B(T,p^k)`: controlling the terms with `k ≥ 2` requires a
prime-power stationary-phase estimate which is not proved here.
-/
variable {p : ℕ} [NeZero p]
end CookMagyarFiniteFourier
end SystolicGrowth
