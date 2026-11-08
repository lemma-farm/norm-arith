/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FinChain
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Absorbing states and the decay of the survival probability -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def IsAbsorbing (a : S) : Prop := C.P a a = 1

def IsAbsorbingSet (A : Finset S) : Prop := ∀ a ∈ A, C.IsAbsorbing a

def survival (A : Finset S) (n : ℕ) (x : S) : ℝ := ∑ y ∈ Aᶜ, C.stepN n x y

def Reaches (A : Finset S) : Prop := ∀ x, ∃ n, ∃ a ∈ A, 0 < C.stepN n x a

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

                                                                                      
                               
                                               

theorem survival_nonneg (C : FinChain S) (A : Finset S) (n : ℕ) (x : S) :
    0 ≤ C.survival A n x :=
  Finset.sum_nonneg fun y _ => C.stepN_nonneg n x y

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

theorem survival_add_le (hA : C.IsAbsorbingSet A) (m n : ℕ) (x : S) :
    C.survival A (m + n) x ≤ C.survival A m x := by
  rw [survival_add hA]
  refine Finset.sum_le_sum fun z _ => ?_
  exact mul_le_of_le_one_right (C.stepN_nonneg m x z) (C.survival_le_one A n z)

theorem survival_antitone (hA : C.IsAbsorbingSet A) (x : S) :
    Antitone fun n => C.survival A n x := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact survival_add_le hA m k x

                                                                   
                                                                       
                                                                   
           
                    
             
                
                          
                                               
                                    
             
                  
                
                          
                                               
                                      
                                                  
                                 
                                         
                                                   
                                                                          
                                                                                    
                                   

theorem Reaches.exists_survival_lt_one (hR : C.Reaches A) (x : S) :
    ∃ n, C.survival A n x < 1 := by
  obtain ⟨n, a, ha, hpos⟩ := hR x
  refine ⟨n, ?_⟩
  have h := C.survival_add_sum A n x
  have : C.stepN n x a ≤ ∑ b ∈ A, C.stepN n x b :=
    Finset.single_le_sum (f := fun b => C.stepN n x b) (fun b _ => C.stepN_nonneg n x b) ha
  linarith

theorem exists_uniform_survival_bound (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x, C.survival A m x ≤ c := by
  choose N hN using hR.exists_survival_lt_one
  set m : ℕ := 1 + ∑ x, N x with hm
  have hlt : ∀ x, C.survival A m x < 1 := by
    intro x
    have hle : N x ≤ m := by
      have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (mem_univ x)
      omega
    exact lt_of_le_of_lt (survival_antitone hA x hle) (hN x)
  refine ⟨m, by omega, ?_⟩
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, le_rfl, zero_lt_one, fun x => (hS.false x).elim⟩
  · obtain ⟨x0, -, hmax⟩ := Finset.exists_max_image univ (fun x => C.survival A m x)
      ⟨hS.some, mem_univ _⟩
    exact ⟨C.survival A m x0, C.survival_nonneg A m x0, hlt x0, fun x => hmax x (mem_univ x)⟩

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

theorem summable_survival (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    Summable fun n => C.survival A n x := by
  obtain ⟨m, hm, c, hc0, hc1, hc⟩ := exists_uniform_survival_bound hA hR
  have hgeom : ∀ q : ℕ, ∑ j ∈ range q, c ^ j ≤ 1 / (1 - c) := by
    intro q
    rw [le_div_iff₀ (by linarith), geom_sum_mul_neg]
    have := pow_nonneg hc0 q
    linarith
  have hblock : ∀ q : ℕ, ∑ i ∈ range (m * q), C.survival A i x ≤ m * ∑ j ∈ range q, c ^ j := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, mul_add]
      refine add_le_add ih ?_
      calc ∑ r ∈ range m, C.survival A (m * q + r) x
          ≤ ∑ _r ∈ range m, c ^ q :=
            Finset.sum_le_sum fun r _ => survival_le_pow hA hc0 hc q r x
        _ = m * c ^ q := by simp
  refine summable_of_sum_range_le (c := m * (1 / (1 - c)))
    (fun n => C.survival_nonneg A n x) fun n => ?_
  calc ∑ i ∈ range n, C.survival A i x
      ≤ ∑ i ∈ range (m * n), C.survival A i x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_mul_of_pos_left n hm))
          fun i _ _ => C.survival_nonneg A i x
    _ ≤ m * ∑ j ∈ range n, c ^ j := hblock n
    _ ≤ m * (1 / (1 - c)) := mul_le_mul_of_nonneg_left (hgeom n) (Nat.cast_nonneg m)

                                                                               
                                                      
                                                

                                                                           
                                                                           
                                                  
                                                                 
                                                    
                                              
                                                              
                       
                                   
                                                                                
                                                              
                                                                

                                                                                           
                                                               
          
                                               
                                                                                     
                                                                  
           
                                               
                                 
                                                                                  
                                                                 
                                                
                             

                                                                                        
                                                                                        
                                                                          
                          

end Rhone.MarkovChain.FinChain
