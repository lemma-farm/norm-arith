/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.ReserveWeights
public import PartitionedTriangleAbsorption.BlowupB.CubeBlocks

/-! # BlowupB.TypicalReserve — the typical reserve exists (binomial random graph)

**`typicalReserveSpec`**: for every family of 3-element types, `TypicalReserveSpec F h` holds.
The reserve is the random subgraph of `E = G \ (B ∪ X)` keeping the pair `uv` with probability
`ρ {p u, p v}` (`rhoM`, scale `θ = eta / (4 t)`), on the finite Bernoulli cube of
`BernoulliExposure`. Degrees, common neighbourhoods and typed-thirds counts are block counts
(`CubeBlocks`); `blockCount_tail` and the union bound over `n + (h+1) 2^h t n^h + |F| n²` events
leave a good outcome for large `n`. Weights and loads come from `ReserveWeights`
(`load_identity`: exact unit loads).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {t : ℕ}

/-! ### Asymptotics -/

                                                                             
                                                                                
                                                            
                                                                            
                                                
                                                   
                                            
                              
                             
                                                         
                                           
                           
                    
                                        
                                                            
                                                                                  
                                                       
                                                                 
                           
                                       
                                          
                                                                                             
             
                                                    
                           
 
                                                                                      
                                                                                     
                       
                                                                      
                                                                           
                                                                              
                                                            
            
 
                      
 
section Coins

variable {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))

/-- The edge of a coin. -/
noncomputable def edgeOf (i : Fin E.card) : Sym2 V := (E.equivFin.symm i).1

                                                                              
 
                                                               
              
                                                  
 
                                                                                          
                
 
                                          
                                                                     
                                                     
 
                                                                   
             
                                        
                       
 
                                                                 
                                              
              
            
                                          
                                      
                               
            
                                                                 
 
                                
                                                                                                             
 
                                                                                       
                                                                       
                   
                                      
                                                      
                                             
                      
                                            
                      
                                                        
                                                                               
                                                 
                 
                  
                                             
                                         
                        
 
                                                                              
                                                             
                                                                 
                                                                
             
                                                      
                                           
                                 
             
                                         
 
                                                                                            
                                                                 
                                               
             
                                                      
                                           
                                 
             
                                         
 
                                                                                        
                                  
             
                                                                 
                 
                                                                     
                                        
                                                         
 
                                                                       
                                                                 
                                                        
                                                      
                  
                                                                                                      
               
                                          
                                                                        
                                                                    
                      
 
                                                                                          
                                                                                          
                                                                        
                                                                     
            
                                                      
                                                         
                                                          
                                                              
                                                            
                                                            
                                                          
                 
          
                  
                                                                           
                            
                  
                                       
                   
         
                      
 
                                                                 
                                                                             
                                                                  
                                                                                  
                           
                                                                          
                                                
                                                    
                                                                                             
                                                                                                 
                                                                                    
                                                            
                   
                                                                           
                                                            
                                                                          
                      
                                                              
           
 
                                                                                            
                           
                                                
                                                           
                    
                                                                                       
                           
 
end Coins

/-! ### Multiset bookkeeping -/

                                                                                      
                                      
                                                                              
                            
 
                                                                                                  
                                                     
                               
                                                      
                                       
                                      
                                       
                 
          
                                                 
                 
                                                  
           
 
end PartitionedTriangleAbsorption.BlowupB
