/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite-alphabet score algebra for the stationary three-tip channel -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
def pairScore (K : ℕ) (a b : Fin K) : ℝ :=
  ((K : ℝ)*(if a = b then 1 else 0) - 1)/(K - 1)
def tripleScore (K : ℕ) (a b c : Fin K) : ℝ :=
  ((K : ℝ)^2*(if a = b ∧ a = c then 1 else 0) -
    K*((if a = b then 1 else 0) + (if a = c then 1 else 0) +
      (if b = c then 1 else 0)) + 2)/((K - 1)*(K - 2))
end Rhone.Statistics.ThreeSiteSeparator
