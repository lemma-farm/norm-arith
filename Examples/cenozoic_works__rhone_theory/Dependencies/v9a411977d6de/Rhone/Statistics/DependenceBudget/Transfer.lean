/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite whole-data transfer bounds; not historical bytes -/
@[expose] public section
open scoped BigOperators
namespace Rhone.Statistics.DependenceBudget
structure Law (X : Type*) [Fintype X] where
  mass : X → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1
variable {X : Type*} [Fintype X]
noncomputable def rejection (P : Law X) (φ : X → ℝ) : ℝ :=
  ∑ x, P.mass x * φ x
structure Coupling (P Q : Law X) where
  mass : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ mass x y
  first : ∀ x, ∑ y, mass x y = P.mass x
  second : ∀ y, ∑ x, mass x y = Q.mass y
end Rhone.Statistics.DependenceBudget
