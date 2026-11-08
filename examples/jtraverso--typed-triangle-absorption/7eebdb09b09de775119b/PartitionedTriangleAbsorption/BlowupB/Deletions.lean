/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Local
public import Mathlib.Tactic.Ring

/-! # BlowupB.Deletions — bounded-cost certificates after deletions

**Theorem** (`physDivCost_local`). For every family `F` of triangle types and every `K` there is
a constant `C = C(F, K)` such that: whenever `G` satisfies the local hypothesis `LocalHyp` with
respect to `5` representatives per class and a vertex predicate `W` covering the vertices of `E`
(every edge of `G` is an allowed pair; every representative is adjacent to every good vertex with
which it forms an allowed pair — all other edges may be deleted), every integrally `F`-divisible
`E ⊆ E(G)` with `|E| ≤ K` has a physical certificate of cost at most `C`.

The constant depends only on `F` and `K`, never on the host. Corollary for complete blowups:
`physDivCost_complete`.

Cost bookkeeping (`physCostZ_local_core`): with `L = |E| + 3 C₁` and `C_g = 4 C₂ L`,
`cost ≤ 8 (L + 3 C_g) + C₁ + C_g`, where `C₁` bounds the edge-count representation and `C₂` the
degree representations (finite boxes, `exists_rep_bound`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} {W : V → Prop}

                                                  
                                                                                          
                                                                                      
                                                                                     
                                     
                                                                       
                                     
                                                                 
                                                                                  
                                                                                
                                         
                                                                                 
                                   
                            
                                                    
                                                           
                                                                  
           
                       
                                                                          
                                      
                                     
                      
                                                                                       
                                                       
                                                    
                                                     
                                                                 
                                                                     
                                                                                  
                          
                                       
                                                                                              
                                                       
                             
                                                                                       
                             
                                                                                             
                                                     
                            
                                   
                                     
                      
            
                                                 
                                      
                                                                          
                                                                                    
                                                              
           
                                                     
                                                                                    
                                   
                                                                                            
                                       
                                    
                                                                                            
                            
          
                                                            
                                                      
                                                                       
                                                                                
                                                                                    
                                                     
                                                                       
             
                                          
                                             
                                                                                   
                                            
                                       
                        
                                                
                                                                         
                                                                                              
                                              
                                                                                  
                                                                     
                                 
                                              
                                                                    
                       
                                                                                     
                                                                
                                                                                  
                                                                        
                        
                                                                               
                   
                         
               
                 
                                       
                                                                  
                 
                    
                       
                                   
                                                                                 
                                        
                                                                
                  
                                                       
                                              
                                                                   
                                                                     
                                 
                                 
                                     
                                                                                     
                                           
           
                                                      
                                                                           
                                                                               
                                        
                                                                                     
                                     
                                                              
                                                  
               
                                                    
                     
                                  
                                     
                 
                
                                                     
           
                                                    
                                       
                                                
                         
                                                                  
                            
                
                                                                               
                                                   
                                                                           
                                                                   
                                       
                                     
                                     
            
                                                                   
                                                                  

end Core

/-! ### Uniform constants -/

                                                                                               
                                                                 
                                                  
                                                                                         
                                                                              
                                                                           
                                                                 
                                                                                           
                                                                                          
                                                                                  
                                                                                
                                        
                                                           
                                 
                                                            
                                                                                       
                                              
                                          
                                
                                                     
                                                                       
                                                                 
                     
               
                          
                                               
                  
              
                             
                     
                                                            
                                
                                                                    

                                                                                                
                      
                                                                    
                                                  
                                                                                         
                                                               
                                                                               
                                   
                                             
                
                                     
                                                                                          

end PartitionedTriangleAbsorption.BlowupB
