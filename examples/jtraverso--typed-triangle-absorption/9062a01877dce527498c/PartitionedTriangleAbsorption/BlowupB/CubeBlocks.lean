/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.CubeTools

/-! # BlowupB.CubeBlocks — block counts on the Bernoulli cube

For a finite family of blocks `B z ⊆ Fin m` (`z ∈ K`), the block count
`blockCount K B ω = #{z ∈ K : every coin of B z is true}` has mean `∑_z ∏_{i ∈ B z} q i`,
changes by at most `#{z ∈ K : i ∈ B z}` when coin `i` is flipped, and therefore obeys the
two-sided rare-coordinate Bernstein bound of `BernoulliConcentration`. Degrees, codegrees and
common neighbourhoods of a random subgraph are block counts.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {m : ℕ}

/-- Indicator of a coin. -/
def coin (ω : Fin m → Bool) (i : Fin m) : ℝ := if ω i then 1 else 0

                                                                       
                                     

                                                                       
                                     

                                                                                           
                                        

                                                                                           
                                                                      

                                                                                      
                             
                                                                     
                                      
                                          
                                             

                                               
                                                                 
                                                                
                                            
                                                             
                       
                       
                                                                                         
                                             
                                                    
                              
              
                                                   

                                                    
def blockCount {ι : Type*} (K : Finset ι) (B : ι → Finset (Fin m)) (ω : Fin m → Bool) : ℝ :=
  ∑ z ∈ K, ∏ i ∈ B z, coin ω i

                                                                                                 
                                                               
                   
                   
                                                           

                                                            
                                                                                   
                                        

                                                                                     
                                                      
           
           
                            
                        
                                          
                                                 
                                 
                   
                                     
               
                                                                  
                                                           
                                                                   
                                                          
                                                                                             

                                                                                       
                                                                         
                                                                                 
                                                                
                                                            
                                                                            
                                                                                     
                                                           
                                         
                                                                         
                                      
                                                                         
                                      
                                   
                                                                             
                                                                             
                                                              
                                        
                                          
                           
                          
                                                          

end PartitionedTriangleAbsorption.BlowupB
