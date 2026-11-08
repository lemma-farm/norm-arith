/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite-state Markov chains in discrete time -/
@[expose] public section
namespace Rhone.MarkovChain
open Finset Matrix
structure FinChain (S : Type*) [Fintype S] where
  P : Matrix S S ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  row_sum : ∀ x, ∑ y, P x y = 1
namespace FinChain
variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)
def expect (f : S → ℝ) : S → ℝ := C.P *ᵥ f
omit [DecidableEq S] in
theorem expect_apply (f : S → ℝ) (x : S) : C.expect f x = ∑ y, C.P x y * f y := rfl
variable {C}
end FinChain
end Rhone.MarkovChain
