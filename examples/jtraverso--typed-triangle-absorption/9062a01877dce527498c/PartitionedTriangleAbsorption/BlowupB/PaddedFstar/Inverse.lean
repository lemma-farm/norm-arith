/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Universal
public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

@[expose] public section

/-!
# The bounded signed inverse for F*

Totals use a new MONOCHROMATIC mode (`monoTypeWeight`, type `iii`) for 000 and 333, together with
repeated and tripartite modes. The type vectors span all seven allowed total coordinates, so no
compatibility condition is needed. Vertex rows and zero rows use only existing modes (no
monochromatic one). The bound `2^20 ε/(γ^6 n)` of the F₁/F₂ inverse is kept.
-/

noncomputable section

namespace PaddedFstar

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-! ### The monochromatic mode -/

/-- Uniform weight `z` of type `iii`, spread over the ordered triples of distinct `V_i`-vertices. -/
def monoTypeWeight (p : V → Fin 4) (i : Fin 4) (z : ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2)) else 0

theorem monoTypeWeight_symmetric (p : V → Fin 4) (i : Fin 4) (z : ℝ) :
    TernarySymmetric (monoTypeWeight p i z) := by
  refine ⟨fun a b c => ?_, fun a b c => ?_⟩ <;> unfold monoTypeWeight
  · by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h2, h1, h3, Ne.symm h4, h6, h5⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨h2, h1, h3, h4, h6, h5⟩
      exact h ⟨h1, h2, h3, Ne.symm h4, h5, h6⟩
  · by_cases h : p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      rw [if_pos ⟨h1, h2, h3, h4, h5, h6⟩, if_pos ⟨h1, h3, h2, h5, h4, Ne.symm h6⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h3, h2, h5, h4, h6⟩
      exact h ⟨h1, h2, h3, h4, h5, Ne.symm h6⟩

theorem monoTypeWeight_supported (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (i : Fin 4)
    (hF : Link F i i i) (z : ℝ) : TernarySupported p F (monoTypeWeight p i z) := by
  intro a b c hbad
  unfold monoTypeWeight
  rw [if_neg]
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  exact hbad ⟨h4, h5, h6, by rw [h1, h2, h3]; exact hF⟩

theorem monoTypeWeight_load (p : V → Fin 4) (i : Fin 4) (z : ℝ)
    (hm : classSize p i ≠ 0) (hm1 : classSize p i - 1 ≠ 0) (hm2 : classSize p i - 2 ≠ 0)
    (a b : V) :
    ternaryLoad (monoTypeWeight p i z) a b =
      constInternalBlock p i (6 * z / (classSize p i * (classSize p i - 1))) a b := by
  classical
  unfold ternaryLoad monoTypeWeight constInternalBlock
  by_cases hab : p a = i ∧ p b = i ∧ a ≠ b
  · obtain ⟨ha, hb, hne⟩ := hab
    rw [if_pos ⟨ha, hb⟩, if_pos hne]
    have hset : (univ.filter fun c => p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) =
        ((classVertices p i).erase a).erase b := by
      ext c
      rw [mem_filter, mem_erase, mem_erase]
      simp only [mem_univ, true_and, classVertices, mem_filter]
      constructor
      · rintro ⟨-, -, h3, -, h5, h6⟩; exact ⟨Ne.symm h6, Ne.symm h5, h3⟩
      · rintro ⟨h6, h5, h3⟩; exact ⟨ha, hb, h3, hne, Ne.symm h5, Ne.symm h6⟩
    have haV : a ∈ classVertices p i := by simp [classVertices, ha]
    have hbV : b ∈ (classVertices p i).erase a := by
      simp [classVertices, hb, Ne.symm hne]
    have hcard : (((classVertices p i).erase a).erase b).card = (classVertices p i).card - 2 := by
      rw [card_erase_of_mem hbV, card_erase_of_mem haV]
      omega
    have hge : 2 ≤ (classVertices p i).card := by
      have h1 := card_erase_of_mem haV
      have h2 : 0 < ((classVertices p i).erase a).card := card_pos.mpr ⟨b, hbV⟩
      omega
    rw [← sum_filter, hset, sum_const, nsmul_eq_mul, hcard]
    have hcast : (((classVertices p i).card - 2 : ℕ) : ℝ) = classSize p i - 2 := by
      unfold classSize; rw [Nat.cast_sub hge]; norm_num
    rw [hcast]
    field_simp
  · have hzero : ∀ c, ¬ (p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
      rintro c ⟨h1, h2, -, h4, -, -⟩; exact hab ⟨h1, h2, h4⟩
    simp only [hzero, if_false, sum_const_zero]
    by_cases h12 : p a = i ∧ p b = i
    · rw [if_pos h12, if_neg]
      intro hne; exact hab ⟨h12.1, h12.2, hne⟩
    · rw [if_neg h12]

theorem monoTypeWeight_totals (p : V → Fin 4) (i : Fin 4) (z : ℝ)
    (hm : classSize p i ≠ 0) (hm1 : classSize p i - 1 ≠ 0) (hm2 : classSize p i - 2 ≠ 0)
    (k l : Fin 4) :
    classTotal p (ternaryLoad (monoTypeWeight p i z)) k l =
      if k = i ∧ l = i then 6 * z else 0 := by
  have he : ternaryLoad (monoTypeWeight p i z) =
      constInternalBlock p i (6 * z / (classSize p i * (classSize p i - 1))) := by
    funext a b; exact monoTypeWeight_load p i z hm hm1 hm2 a b
  rw [he, classTotal_constInternalBlock]
  split_ifs
  · field_simp
  · rfl

theorem mono_normalizer_bound (p : V → Fin 4) (i : Fin 4) (z E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz : |z| ≤ 2 * E) (hm : ∀ i, δ ≤ classSize p i) :
    |6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2))| ≤ 32 * E / δ ^ 3 := by
  have hmi := hm i
  set m := classSize p i with hmdef
  have hd : 0 < δ := by linarith
  have hm0 : 0 < m := by linarith
  have h1 : 3 * m / 4 ≤ m - 1 := by linarith
  have h2 : m / 2 ≤ m - 2 := by linarith
  have hden : 3 * δ ^ 3 / 8 ≤ m * (m - 1) * (m - 2) := by
    have hδm : δ ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ hd.le hmi 3
    have hprod : m * (3 * m / 4) * (m / 2) ≤ m * (m - 1) * (m - 2) := by
      have hA : m * (3 * m / 4) ≤ m * (m - 1) := mul_le_mul_of_nonneg_left h1 hm0.le
      exact mul_le_mul hA h2 (by positivity) (by nlinarith)
    nlinarith
  have hdenpos : 0 < m * (m - 1) * (m - 2) := lt_of_lt_of_le (by positivity) hden
  rw [abs_div, abs_of_pos hdenpos, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
  rw [div_le_div_iff₀ hdenpos (by positivity)]
  have h6 : 6 * |z| ≤ 12 * E := by linarith
  nlinarith [mul_le_mul h6 hden (by positivity) (by positivity)]

/-! ### Stage 1: totals -/

                                                                             
                                                                                        
 
                                                                   
                                                                   
                                                                               
                                                                                          
                                 
                                                                                          
                                                                                          
                                                                                          
             
                                  
                                                              
                                                                            
                                                                            
                                                        
 
                                                                                     
                                                                    
                                                                              
                                                                              
                                                                  
 
                                                                                  
                                                                       
                         
                
                                           
                                                 
                                                     
                                 
 
                                                                                  
                                                                               
                         
                
                                                                                
                                                                                       
                                                                                
                                         
                                 
 
                                                                             
                                                                     
                                         
                                                                             
                                                                                       
                                                                     
             
                         
                                     
                                                                                
                                                                                      
                                                                                           
                          
                                                                  
 
                                                                                
                              
                                              
                                                       
                                                
                                                                             
                                                
                                                                   
                                         
                                                       
              
                                              
                        
                          
                            
                                   
             
                                                
                                                         
                                                         
                                                           
                                                           
                                                                                   
                                                                                   
                                                                                       
                                                                                       
                                                                                   
                                                                                   
                                                                   
                                                                              
                          
                          
                          
                                                  
                         
                  
               
               
               
               
               
               
               
               
               
 
                                                                               
                                                            
                                                                 
                                                 
                         
                                                        
                                                      
                                                
                                     
                                     
                                     
                                     
                                     
                                     
                                     
                                                                               
                                   
                                   
                  
                               
                                                          
                                                          
                                                                            
                                
                                
                                                                   
                                
                                                                   
                                                              
               
                                                                
                                                         
                                                                                            
                                                                       
                                                                            
                                                                            
                                                                                                  
                                                     
                                                                     
                                                                                                   
                                                                   
 
                                
 
                                                                             
                                  
                                                                            
                                                                            
                                                                                
                                  
                                                                            
                                                                            
                                                                                
                                  
                                                          
                                                                     
                                                           
                                  
                                                          
                                                                     
                                                         
 
                                                                          
                                                   
                           
                
                                                   
                                                    
                                                       
                                 
 
                                                                          
                                                           
                           
                
                                                                                       
                                                                                
                                         
                                 
 
                                                                   
                                                                       
                                                                     
                                                             
                                                                       
                                
                                                                                                  
                  
                                                                                              
                                                                                        
                
                                                                   
                                                                            
                                            
                           
                                   
                                                                     
                                                                   
                                                                      
                                                                   
                                                                   
                                                                      
                                                                  
                                                                  
                                                                
                                                                  
                                                                  
                                                                
                       
                                     
                                       
                  
                                                        
           
 
                                                                              
                                                        
                                                
                                                          
                                        
                                                                                            
                                                                                              
                                                   
                                                       
                                                                                
                                                    
                                                    
                                                        
                                                    
                                                    
                                                        
                                                 
                                                             
                                                    
                                                   
                                                    
                                                  
                                                              
                                                    
                                                    
                                                    
                           
                                                                        
             
                                                                                  
                                                          
                                                                                        
                                                                                              
 
                              
 
                                                                          
                                                                        
                                                                        
                                                                            
                                   
 
                                                                     
                                                                                  
                            
                
                                                    
                                                 
                                        
                                 
 
                                                                       
                                                            
                            
                
                                                                                       
                                                                                
                                         
                                 
 
                                                                
                                                                               
                                                                  
                                                                                 
                                                           
                                                                               
                                                                                
                                                                                     
                            
                                                
                      
                                  
                                  
                                       
                                                           
 
                                                                           
                                                        
                                                
                                                      
                                                                   
                    
                    
                    
                    
                      
                    
                    
                                   
                                      
               
                                                     
          
                                                           
                            
                                        
                                                                                        
                            
 
                                                    
 
                                                                                
                                            
                                            
                                                           
                                                        
                                                               
                                                                           
                                           
                                                                                   
                              
                        
                                                                                
                                  
                                  
                                                 
                                                   
                                                                         
                                                                              
                                                                              
                                                                                  
                                                                         
                          
                                                          
                                   
                          
         
                                                                                
                          
         
                                     
                                                                                             
                           
                                                                                       
                                                              
                                                                          
                                                                                     
                                                                                   
                                                             
                         
                                                                      
                                                                                           
                  
                                                                             
                                              
                               
                                                                           
                                                                                                
                  
                                                                          
                                 
                                           
                                                                   
 
                                                                               
                                                                                  
                                                    
                                                                                               
                                                                                        
                            
                                                                                 
                            
                                                                                                
            
                                    
               
                           
                
                                     
                                            
                                                                   
                                                                               
             
                                                                                              
            
                                                                 
                                                                
                                                           
                 
 
                                    
                                            
                                        
 
end PaddedFstar
