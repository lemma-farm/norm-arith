/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.vb79371728a95.Rhone.MarkovChain.FinChain
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
def IsAbsorbingSet (A : Finset S) : Prop := ∀ a ∈ A, C.IsAbsorbing a
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
theorem survival_add_sum (C : FinChain S) (A : Finset S) (n : ℕ) (x : S) :
    C.survival A n x + ∑ a ∈ A, C.stepN n x a = 1 := by
  rw [survival, add_comm, Finset.sum_add_sum_compl, C.stepN_row_sum]
theorem survival_le_one (C : FinChain S) (A : Finset S) (n : ℕ) (x : S) :
    C.survival A n x ≤ 1 := by
  have h := C.survival_add_sum A n x
  have : 0 ≤ ∑ a ∈ A, C.stepN n x a := Finset.sum_nonneg fun y _ => C.stepN_nonneg n x y
  linarith
theorem survival_of_mem (hA : C.IsAbsorbingSet A) {a : S} (ha : a ∈ A) (n : ℕ) :
    C.survival A n a = 0 := by
  refine Finset.sum_eq_zero fun y hy => ?_
  have hne : a ≠ y := fun h => (mem_compl.1 hy) (h ▸ ha)
  simp [(hA a ha).stepN_apply, hne]
theorem survival_add (hA : C.IsAbsorbingSet A) (m n : ℕ) (x : S) :
    C.survival A (m + n) x = ∑ z ∈ Aᶜ, C.stepN m x z * C.survival A n z := by
  have h1 : C.survival A (m + n) x = ∑ z, C.stepN m x z * C.survival A n z := by
    simp only [survival, stepN_add_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [h1, ← Finset.sum_add_sum_compl A]
  have : ∑ z ∈ A, C.stepN m x z * C.survival A n z = 0 :=
    Finset.sum_eq_zero fun z hz => by rw [survival_of_mem hA hz, mul_zero]
  rw [this, zero_add]
theorem survival_le_pow (hA : C.IsAbsorbingSet A) {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, C.survival A m x ≤ c) (q r : ℕ) (x : S) :
    C.survival A (m * q + r) x ≤ c ^ q := by
  induction q generalizing x with
  | zero => simpa using C.survival_le_one A r x
  | succ q ih =>
    have e : m * (q + 1) + r = m + (m * q + r) := by ring
    rw [e, survival_add hA]
    calc ∑ z ∈ Aᶜ, C.stepN m x z * C.survival A (m * q + r) z
        ≤ ∑ z ∈ Aᶜ, C.stepN m x z * c ^ q :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ih z) (C.stepN_nonneg m x z)
      _ = C.survival A m x * c ^ q := by rw [survival, Finset.sum_mul]
      _ ≤ c * c ^ q := mul_le_mul_of_nonneg_right (hc x) (pow_nonneg hc0 q)
      _ = c ^ (q + 1) := by ring
end Rhone.MarkovChain.FinChain
