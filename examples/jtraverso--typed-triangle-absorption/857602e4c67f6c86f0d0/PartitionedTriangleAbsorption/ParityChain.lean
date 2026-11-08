/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.OnePartDivisibility

/-!
# The parity chain (building block of the hub-hierarchy parity refiner)

Positions `0, …, N-1` carry bits `x j`. Between positions `j` and `j+1` there is a wire made of
two edge sets `A j`, `Bw j`, each odd exactly at the two roots `a`, `b`.
The carry is `c j = (x 0 + … + x j) mod 2`.

Position `j` receives:
* `Bw (j-1)` when `c (j-1) = 1`;
* from wire `j`, `A j` when `c j = 1`, and `A j ∪ Bw j` when `c j = 0`.

This file proves the chain mechanism of `REFINER_STATUS.md` §3.1:
* the received sets are pairwise disjoint (`recv_disjoint`);
* together they use every wire exactly once (`recv_union`);
* the received set at `j` is odd exactly at `a, b`, and only when `x j = 1`, except at the
  last position, where the final carry is added (`recv_parity`).

This is only the chain mechanism. The hub-level assembly (Lemma H) and the hierarchy
(Theorem P) are not formalised.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ParityChain

open Finset AntiEdgeSelection OnePart

variable {V : Type*} [DecidableEq V]

/-- Carry: parity of the number of set bits among positions `0..j`. -/
def carry (x : ℕ → Bool) (j : ℕ) : ℕ := ((range (j + 1)).filter fun i => x i = true).card % 2

                                          
                                                                                         
                                                           
                                                                          

                                  
                                                             

                               
                                                                               
                                                             
                                                                     
                                                                       
                                                                    
                                                                     

variable {N : ℕ} {x : ℕ → Bool} {A Bw : ℕ → Finset (Sym2 V)} {a b : V}

theorem carry_lt (x : ℕ → Bool) (j : ℕ) : carry x j < 2 := Nat.mod_lt _ (by norm_num)

theorem carry_zero (x : ℕ → Bool) : carry x 0 = if x 0 then 1 else 0 := by
  cases h : x 0 <;> simp [carry, range_one, filter_singleton, h]

theorem carry_succ (x : ℕ → Bool) (j : ℕ) :
    carry x (j + 1) = (carry x j + if x (j + 1) then 1 else 0) % 2 := by
  unfold carry
  rw [range_add_one (n := j + 1), filter_insert]
  cases h : x (j + 1)
  · simp
  · simp only [ite_true]
    rw [card_insert_of_notMem (by simp)]
    omega

                                       
                                                                          
                                                                
             
                
             
                    
                             
                                     
                  
                                
                                    
                                           
                                      
                                            
                  
                                               
                                               
                                                         
                                                                             

                                                                                       
                                                                        
                    
                
                                                                   
                                                                       
                                                                                  
                                                                       
                             
                                  
                                                                             
                                                                       
                                                                           
                                                                       
                             
                                  
                                                                             
                                                                       
                                                                           

                                                                                 
                    
                                                                                         
       
                                               
             
                      
                                                               
                                        
                                    
                                    
                           
                                                                      
                                 
                                                                                  
                              
                                                                              

                                                                              
                                                                                          
                                   

                                                    
                                        

                                                                                           
                                                                                     
                                                                             
                                          
                                                                                                 
                                            
                                                                               
                                                                                  
                      
                  
                                             
                               
                             
                                  
                                      
                                                                            
                                       
                                                                                       
                                
                      
                                              
                       
                       
                                                
                                            
                                                                                         
                                                                      
                                  
                                             
                                                                                      
                             
                          
                                                                               
               
                         
                                              
                                           
                            
                                                                                        
                                                                                    
                            
                           
                                         
                                 
                                                                                    
                                                                                  
                                                     
                                        
                        
                                                                
             
                                     
                                       
                                       
                                          
            
                            
                           
                                      
                                                                    
                                                                        
                                  
                                                                    
                                                                        
                                                         
                              
                            
                                   
                                                   
                               
                                          
                                            
                                                                                           
             
                                      
                                            
                                                                                           
             

end PartitionedTriangleAbsorption.ParityChain

