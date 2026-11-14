module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecificLimits.Basic

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.v1c21be0a792d.Rhone.MarkovChain.FinChain ====
public section
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
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

def stepN (n : ℕ) : Matrix S S ℝ := C.P ^ n

def expectN (n : ℕ) (f : S → ℝ) : S → ℝ := C.stepN n *ᵥ f

set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.stepN_nonneg.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : DecidableEq S] (C : Rhone.MarkovChain.FinChain S)
  (n : ℕ) (x y : S), 0 ≤ C.stepN n x y

variable {C}

end FinChain
end Rhone.MarkovChain

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_200e793d7eea9483c855_Absorption ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Absorbing states and the decay of the survival probability -/
@[expose] public section
namespace Rhone.MarkovChain.FinChain
open Finset Filter Topology
variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def survival (A : Finset S) (n : ℕ) (x : S) : ℝ := ∑ y ∈ Aᶜ, C.stepN n x y
variable {C} {A : Finset S}


set_option linter.unusedVariables false in
theorem abs_expectN_le_survival (C : FinChain S) {A : Finset S} {g : S → ℝ}
    (h0 : ∀ a ∈ A, g a = 0) {M : ℝ} (hM : ∀ y, |g y| ≤ M) (n : ℕ) (x : S) 
    (h_Rhone_MarkovChain_FinChain_expectN_apply : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : DecidableEq S] (C : Rhone.MarkovChain.FinChain S)
      (n : ℕ) (f : S → ℝ) (x : S), C.expectN n f x = ∑ y : S, C.stepN n x y * f y)
    :
    |C.expectN n g x| ≤ M * C.survival A n x := by
  have h1 : C.expectN n g x = ∑ y ∈ Aᶜ, C.stepN n x y * g y := by
    rw [h_Rhone_MarkovChain_FinChain_expectN_apply, ← Finset.sum_add_sum_compl A]
    have : ∑ y ∈ A, C.stepN n x y * g y = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [h0 y hy, mul_zero]
    rw [this, zero_add]
  rw [h1, survival, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (C.stepN_nonneg n x y), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM y) (C.stepN_nonneg n x y)
end Rhone.MarkovChain.FinChain
