/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic

/-! The planar simple-walk kernel satisfies exact convolution and reflection identities. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Polymer

                                                             
                                                      
                               
                                                           
                                                                   
                                             

                                                          
def oppositeStep : Fin 4 ≃ Fin 4 where
  toFun i := ![1, 0, 3, 2] i
  invFun i := ![1, 0, 3, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Opposite walk directions have opposite step vectors. -/
theorem srwStep_opposite (i : Fin 4) :
    srwStep (oppositeStep i) = -srwStep i := by
  fin_cases i <;> decide

/-- Reversing every step direction negates the walk displacement. -/
theorem walkPosition_opposite {n : ℕ} (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition 0 (fun i => oppositeStep (s i)) j = -walkPosition 0 s j := by
  simp only [walkPosition, srwStep_opposite, Finset.sum_neg_distrib, zero_add]

/-- The simple-walk kernel is invariant under spatial negation. -/
theorem srwKernel_neg (n : ℕ) (z : Site) :
    srwKernel n (-z) = srwKernel n z := by
  unfold srwKernel
  let e : (Fin n → Fin 4) ≃ (Fin n → Fin 4) :=
    Equiv.piCongrRight (fun _ => oppositeStep)
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  have he : e s = fun i => oppositeStep (s i) := rfl
  rw [he, walkPosition_opposite]
  simp only [neg_inj]

/-- The simple-walk kernel is unchanged when the two displacement endpoints are exchanged. -/
theorem srwKernel_sub_swap (n : ℕ) (w z : Site) :
    srwKernel n (w - z) = srwKernel n (z - w) := by
  rw [← neg_sub z w, srwKernel_neg]

                                                                                        
                                                  
                                                       
                                     
                                     
                  
         
                               

                                                                         
                                                             
                                 
                                           
                                            
                                                                          
                                                                 
                                                                     

                                                                                 
                                                                                  
                                                         
                                          
                                                      

                                                                                      
                                                          
                                                    
                                       
                                                           
                                                      
                   
                                                             
                                                 
                                 
                                                                            
           
                                   
                   
         
         
                            
           
                                                                    

                                                                              
                                                                       
                                  
                              
                                                             
                                                        
                          
                                                              
                            
                            
           
                              
                                                                
                                          
                            
           
                                
      

                                                                                
                                                         
                                   
                                                  
                              
                                                             
                                                                      
                                 
                                                                
                          
                            
           
                                                    
                                                                                      
                     
                            
           
                                                        
      


end Critical2DKPZ.Polymer
