-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.Amnr.Calculus
public import Mathlib
/-! Induction infrastructure for the AMNR tensors. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

                                                                         
                                                                                 
                                                              
                                                             
                                                                     
                                          
                                          
                                      
                                   
                                                                     
                                                    
                                                                    
                                                                           
                                   
           
                                     
                                                                                
                 
                
                                              
                                        
                                                                        
                                                                            
                                                                   
                                      
                                          

                                                                             
                                  
                                                             
                                                             
                                                                     
                                          
                                          
                                      
                                   
                                                                     
                                                    
                                                                    
                                                                     
                                                       
                                                    
                                                    
                      
                                                                                    
                                              
                                                                        
                                                       
                                                                                           
                          
                                                           
                                                                 
                                                                            
                                                                 
                                                                     
            
                                                                    
                                                                                        
                                                                   
                                                                     
                                                
                                                                            
         

                                                                       
                                                                               
                                                                  
                                                        
                                                   
                                                           
                                                                         
                                                                     
                                                       
                                        
                                                    
                                                                  
                                              
                                                              
                                                                         
                                                
                                                             
                                                 
                                                                        
              
                                                                  
                                              
                                                     
                           
                                                                  
                                    
                                           
                                                    
                                                                   
                                                             
                                                     
                                    
                                                                          
                                   
                                                                 
                                                          
                                                                                
                                                                     
         
               
          
      

                                                                       
theorem amnrBudget_sublist {v w : List (Option (Fin 2))} (h : v.Sublist w) :
    amnrBudget v ≤ amnrBudget w := by
  unfold amnrBudget
  exact (h.map _).sum_le_sum (by intro a ha; exact Nat.zero_le a)

                                                                           
                                                                              
                                                                               
                                 
                                                               
                                                        
                                                             
                                                                     
                                          
                                                                             
                                   
                                                                     
                                                    
                                                                    
                                              
                                            
                                                                   
                                                      
                                                        
                                                                               
                                                                       
                                                           
                                                                
                                                      
                                        
                                                 
                                                                    
                          
                        
                         
                                  
                                                     
                                                               
                                                                  
                                   
           
                                           
                                         
                                                          
                                                                          
                
                                                     
                             
                                 
                                                                            
                  
                                         
                                                
                  
                                                                       
                
                                          
                                       
                                                                              
                                               
                                                      
                                                    
                                                                          
                                
                             
                                                      
                                                                            
                       
                      
                  
                                                                                
                                                      
                                                                          
                                                      
                                                       
                                                                          
                                                                             
                                       
                                                  
                                                  
                                             
                                                    
                                                                      
                                                            
                                                                          
                
                                                    
                                                                
                                                                     
                                        
                                                                   
                                        
                                        
                                                             
           
                        
                           
        

                                                                          
                                                                     
def amnrMixedWord (α : List (Fin 2)) (ℓ : ℕ) : List (Option (Fin 2)) :=
  α.map some ++ List.replicate ℓ none

theorem amnrMixedWord_mixed (α : List (Fin 2)) (ℓ : ℕ) :
    IsAmnrMixedWord (amnrMixedWord α ℓ) := by
  unfold IsAmnrMixedWord amnrMixedWord
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_map.mpr
    exact List.pairwise_of_forall (by simp)
  · exact List.pairwise_replicate.mpr (by simp)
  · simp

theorem amnrMixedWord_budget (α : List (Fin 2)) (ℓ : ℕ) :
    amnrBudget (amnrMixedWord α ℓ) = α.length + 2 * ℓ := by
  unfold amnrMixedWord
  rw [amnrBudget_append]
  simp [amnrBudget, List.map_map, List.sum_replicate, Nat.mul_comm, Function.comp_def]

theorem amnrMixedWord_weight (S H : ℝ) (α : List (Fin 2)) (ℓ : ℕ) :
    amnrWeight S H (amnrMixedWord α ℓ) = S ^ α.length * H ^ ℓ := by
  simp [amnrMixedWord, amnrWeight, List.map_map, Function.comp_def]

end AVenhance.Infra.Section4
