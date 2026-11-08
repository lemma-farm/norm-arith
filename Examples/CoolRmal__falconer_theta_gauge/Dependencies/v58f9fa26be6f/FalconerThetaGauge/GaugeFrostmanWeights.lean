/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostmanDyadic
public import Mathlib
set_option autoImplicit false
/-!
# Finite dyadic Frostman normalization for positive capacities

Adapted from `FalconerPacking.FrostmanWeights` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/FrostmanWeights.lean
The construction is generalized from power allowances to any positive sequence
of capacities. Starting with the finest capacity, it repeatedly scales down
weights in overfull ancestors. Every generation satisfies its capacity, every
occupied finest cube retains a saturated ancestor, and maximal saturated cubes
have disjoint fibres whose capacities sum to at most the remaining total mass.
-/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge.GaugeFrostman
/-- The positive capacity prescribed at each dyadic generation. -/
structure PositiveCapacity where
  value : ℕ → ℝ
  positive : ∀ j, 0 < value j
variable (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : PositiveCapacity)
section Saturation
variable {S n d}
end Saturation
section Invariant
variable {S n d}
end Invariant
section MaximalSaturated
variable {S n d}
end MaximalSaturated
section MassBound
variable {S n d}
end MassBound
end FalconerThetaGauge.GaugeFrostman
