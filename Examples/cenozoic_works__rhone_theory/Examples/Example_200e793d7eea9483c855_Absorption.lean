/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v1c21be0a792d.Rhone.MarkovChain.FinChain
public import Mathlib.Analysis.SpecificLimits.Basic
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
def survival (A : Finset S) (n : ℕ) (x : S) : ℝ := ∑ y ∈ Aᶜ, C.stepN n x y
variable {C} {A : Finset S}
theorem IsAbsorbing.P_apply {a : S} (ha : C.IsAbsorbing a) (y : S) :
    C.P a y = if a = y then 1 else 0 := by
  split_ifs with h
  · rw [← h]; exact ha
  · have hsum := C.row_sum a
    rw [← Finset.add_sum_erase _ _ (mem_univ a), show C.P a a = 1 from ha] at hsum
    have hz : ∑ y ∈ univ.erase a, C.P a y = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => C.nonneg a y).1 hz y
      (mem_erase.2 ⟨fun hya => h hya.symm, mem_univ y⟩)
theorem IsAbsorbing.stepN_apply {a : S} (ha : C.IsAbsorbing a) (n : ℕ) (y : S) :
    C.stepN n a y = if a = y then 1 else 0 := by
  induction n with
  | zero => simp [stepN_zero, Matrix.one_apply]
  | succ n ih =>
    rw [stepN_succ, Matrix.mul_apply]
    simp [ha.P_apply, ih]
theorem IsAbsorbing.expectN_apply {a : S} (ha : C.IsAbsorbing a) (n : ℕ) (f : S → ℝ) :
    C.expectN n f a = f a := by
  simp [FinChain.expectN_apply, ha.stepN_apply]
theorem abs_expectN_le_survival (C : FinChain S) {A : Finset S} {g : S → ℝ}
    (h0 : ∀ a ∈ A, g a = 0) {M : ℝ} (hM : ∀ y, |g y| ≤ M) (n : ℕ) (x : S) :
    |C.expectN n g x| ≤ M * C.survival A n x := by
  have h1 : C.expectN n g x = ∑ y ∈ Aᶜ, C.stepN n x y * g y := by
    rw [expectN_apply, ← Finset.sum_add_sum_compl A]
    have : ∑ y ∈ A, C.stepN n x y * g y = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [h0 y hy, mul_zero]
    rw [this, zero_add]
  rw [h1, survival, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (C.stepN_nonneg n x y), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM y) (C.stepN_nonneg n x y)
end Rhone.MarkovChain.FinChain
