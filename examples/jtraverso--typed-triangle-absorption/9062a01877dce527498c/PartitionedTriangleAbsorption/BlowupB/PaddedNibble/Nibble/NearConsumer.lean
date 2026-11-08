/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.Consumer

/-! # Nibble from approximate loads with an explicit degree gap

The initial error is chosen before the graph. A positive gap in the initial
maximum degree permits starting the accepted invariant at time one. The
weights are shifted back by `exp (-2γ)`; all subsequent rounds use the existing
`IterInv.step`, not a second implementation of the probabilistic argument.
This produces a packing, not an absorber or a decomposition of the whole graph.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/NearConsumer.lean.
Original SHA256: 8cac7ff1e467171157bc515a70d27a5810a73b7f286d2027fa5d6bbfcd9a8bd7.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open Finset

theorem IterInv.start_near {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (γ θ c a : ℝ) (hB : ∀ i, triEdges (S.tri i) ⊆ B)
    (hdeg : ∀ v, ((star B v).card : ℝ) ≤ (1 - γ / 8) * Fintype.card V)
    (hload : ∀ e ∈ B, |S.load w e - 1| ≤ c * a) :
    IterInv S B (fun i => Real.exp (-2 * γ) * w i) γ θ c a 1 univ B ∅ ∅ where
  alive_sub i _ := hB i
  pack := by simp [IsPacking]
  disj := by simp [edgesOf]
  cover := by simp [edgesOf]
  waste v := by
    simp only [star, filter_empty, card_empty, Nat.cast_zero, Nat.cast_one, mul_one]
    positivity
  deg v := Or.inr (by simpa using hdeg v)
  load e he := by
    have hw : ∀ i, Real.exp (2 * γ) * (Real.exp (-2 * γ) * w i) = w i := by
      intro i
      rw [← mul_assoc, ← Real.exp_add]
      simp
    simp only [Nat.cast_one, mul_one, pow_one, aliveLoad, hw]
    exact hload e he

                                                                            
                                                              
                                                                 
                  
                                         
                                                                    
                                                                          
                                                        
                                         
                                                                 
                                         
                                             
                                                                               
                                
                                                                        
                                     
                                                                
                                                                     
                                                                        
                                                 
                            
                                                          
             
                        
                                            
                                  
                                              
                                                              
                            
                                          
                                                            
                                                                                
            
                                          
                                                      
                                                                          
                                   
                                                               
                                              
                                                                                               
                                                                                              
                                                                
                                                    
                                                                            
                               
                                                        
                                                                              
                                                  
           
                                       
                                                                            
                                                          
                                 
                                                                           
                                                     
           
                    
                   
                  
                   
                         
               
                                                                            
                 
                                                                                  
                    
                                                                      
                                                          
                                                                     
                                            
                                                     
                                
                                                                            
                                                   
                                            
                                                                   
                                                                        
                                                  
                                                          
                
                                                           
                                              
                                                                           
                 
                                                                      
                                                                           
                                                                     
                                                          
                    
                                                    
                                                              
                                                                      
                                                           
                       
                                
                                                                        
                               
                                                                               
                                                                                   
                                              
                                  
                                                                                   
                                                                          
                                                                                             
                     
                                                                 
                              
                
                                                              
                                                                
                                
                                                      
            
                                                 
           

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
