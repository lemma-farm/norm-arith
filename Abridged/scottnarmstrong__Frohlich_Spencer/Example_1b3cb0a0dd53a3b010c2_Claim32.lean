module

public import Mathlib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.SpecificLimits.Basic

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_1b3cb0a0dd53a3b010c2_Claim32 ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# KP Claim 3.2

For an ensemble satisfying
properties (1)–(3) of the Theorem 1.6 and `β` below an explicit threshold,
`∑_{ϱ ∈ 𝒩} |z(ϱ)| ⟨σ, ϱ⟩² ≤ (β / D) ∑_e (∇_e σ)²`.

The proof has three steps:
* route each density through its domain `D_j(ϱ)` (`Multigraph.exists_integer_routing`);
* apply Cauchy–Schwarz on the edges inside the domain, whose number is at most
  `K₀ (d(ϱ) + 1)²` (`K₀ = 144` on the free and periodic squares, from
  `Charges/DensityBall.lean` and a neighbour count);
* use the T1.6 damping `|z| ≤ exp(-(c₁/β)(‖ϱ‖₂² + log₂(d+1)))` through a β threshold,
  then group by the scale `2^k ≤ d + 1 < 2^{k+1}`.

Within a scale the domains are disjoint
  (T1.6 (3)), and `∑_{k ≥ 1} 2^{-k} ≤ 1`.

The threshold is a hypothesis here; `ExpMoment/Claim32Threshold.lean` provides it.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT
open Finset
universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
namespace Multigraph

end Multigraph

/-- The ℓ¹ norm of an integer density is at most its squared ℓ² norm. -/
theorem sum_abs_le_sum_sq (ρ : V → ℤ) : (∑ j, |(ρ j : ℝ)|) ≤ ∑ j, (ρ j : ℝ) ^ 2 := by
  refine Finset.sum_le_sum fun j _ => ?_
  have h : |ρ j| ≤ ρ j ^ 2 := by
    rcases eq_or_ne (ρ j) 0 with h0 | h0
    · simp [h0]
    · nlinarith [Int.one_le_abs h0, sq_abs (ρ j)]
  have : ((|ρ j| : ℤ) : ℝ) ≤ ((ρ j ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
  simpa using this

/-!
### The edge-volume bound on the square domains
-/

end FroehlichSpencer.BKT
end
