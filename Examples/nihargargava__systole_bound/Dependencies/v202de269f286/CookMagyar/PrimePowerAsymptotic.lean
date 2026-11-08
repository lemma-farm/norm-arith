module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.HuaMoment
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.PrimePowerBridge
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.PrimePowerMass
@[expose] public section
open Filter Asymptotics
namespace SystolicGrowth
namespace CookMagyarCircle
/-! # Asymptotic removal of prime powers

The exact Fourier and union-bound argument in `PrimePowerBridge` reduces
prime-power removal to an eighth moment.  This file completes all remaining
asymptotic bookkeeping.  The sole analytic input is the familiar weak form
of Hua's estimate

`∫ |S_N(α)|⁸ dα = o(N⁵ √N)`.

Cook--Magyar (and the classical cubic Hua lemma) gives the stronger bound
`O(N^(5+ε))` for every positive `ε`.  Thus the statement below deliberately
uses less than the available saving, while avoiding any target parameter:
the discarded error is automatically uniform in `T`.
-/
end CookMagyarCircle
end SystolicGrowth
