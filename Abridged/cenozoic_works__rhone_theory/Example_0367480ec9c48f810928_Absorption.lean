module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecificLimits.Basic

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.vf406ab0d2ccc.Rhone.MarkovChain.FinChain ====
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

set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.stepN_nonneg.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : DecidableEq S] (C : Rhone.MarkovChain.FinChain S)
  (n : ℕ) (x y : S), 0 ≤ C.stepN n x y

variable {C}

end FinChain
end Rhone.MarkovChain

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_0367480ec9c48f810928_Absorption ====
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
def IsAbsorbing (a : S) : Prop := C.P a a = 1
def IsAbsorbingSet (A : Finset S) : Prop := ∀ a ∈ A, C.IsAbsorbing a
def survival (A : Finset S) (n : ℕ) (x : S) : ℝ := ∑ y ∈ Aᶜ, C.stepN n x y
variable {C} {A : Finset S}

set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.survival_le_one.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : DecidableEq S] (C : Rhone.MarkovChain.FinChain S)
  (A : Finset S) (n : ℕ) (x : S), C.survival A n x ≤ 1


set_option linter.unusedVariables false in
theorem survival_add_le (hA : C.IsAbsorbingSet A) (m n : ℕ) (x : S) 
    (h_Rhone_MarkovChain_FinChain_survival_add : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : DecidableEq S] {C : Rhone.MarkovChain.FinChain S}
      {A : Finset S},
      C.IsAbsorbingSet A →
        ∀ (m n : ℕ) (x : S), C.survival A (m + n) x = ∑ z ∈ Aᶜ, C.stepN m x z * C.survival A n z)
    :
    C.survival A (m + n) x ≤ C.survival A m x := by
  rw [h_Rhone_MarkovChain_FinChain_survival_add hA]
  refine Finset.sum_le_sum fun z _ => ?_
  exact mul_le_of_le_one_right (C.stepN_nonneg m x z) (C.survival_le_one A n z)
end Rhone.MarkovChain.FinChain
