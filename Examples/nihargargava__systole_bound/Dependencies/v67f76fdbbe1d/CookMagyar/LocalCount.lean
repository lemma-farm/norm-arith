module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.FiniteFourier
public import Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.LocalNonsingular
public import Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.LocalSmallPrimes
@[expose] public section
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarFiniteFourier
/-! # Local solutions and normalized congruence counts

This file connects the explicit unit solutions from `LocalNonsingular` to
the exact finite Fourier count.  It also defines the finite-level
normalization whose prime-power limit is the local factor in the singular
series.
-/
variable {q : ℕ} [NeZero q]
end CookMagyarFiniteFourier
end SystolicGrowth
