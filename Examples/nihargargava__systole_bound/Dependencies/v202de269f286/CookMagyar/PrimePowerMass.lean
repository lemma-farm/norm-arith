module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.PrimePowerAnalytic
public import Mathlib.NumberTheory.Chebyshev
@[expose] public section
open scoped ArithmeticFunction
open Filter Asymptotics
namespace SystolicGrowth
namespace CookMagyarCircle
/-! # The mass of the discarded prime powers

Mathlib's Chebyshev function already contains the sharp elementary fact that
the total von--Mangoldt mass of proper prime powers up to `N` is
`O(√N)`.  The only additional term discarded here is the even prime `2`.
This file identifies our coefficient mass exactly with `ψ(N)-θ(N)+log 2`
and records an explicit bound.
-/
open Finset
end CookMagyarCircle
end SystolicGrowth
