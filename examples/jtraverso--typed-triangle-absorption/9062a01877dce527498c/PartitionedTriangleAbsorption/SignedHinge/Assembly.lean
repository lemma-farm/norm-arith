/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups

/-! # Two-mode assembly of a signed certificate (abstract cancellation mechanism)

This is the cancellation/multiplicity mechanism, stated abstractly and generically in `F`.

* `O` is the set of **occurrences** (a certificate term `c_j t_j` contributes `|c_j|`
  occurrences of `t_j`), each with a sign `pos o`.
* `S` is the set of **slots** (one per edge of each occurrence), `occ σ` its occurrence.
  Each slot carries a *wedge* `W σ` (the two edges joining its base edge to its apex).
* Every occurrence carries a *local closure* `Y o` such that both `Y o` and
  `R o = Y o ∪ ⋃_{σ ∈ o} W σ` are decomposable (the occurrence gadget).
* A bijection `μ` between positive slots and `P ⊕ negative slots` pairs every positive slot
  either with an edge of `P` (whose triangle with the slot wedge is decomposable) or with a
  negative slot `τ`; each negative slot carries a *slot hinge* `H τ` with both
  `H τ ∪ W τ` and `H τ ∪ W (μ⁻¹ τ)` decomposable.

Then, with all atoms pairwise edge-disjoint, `X = ⋃ Y ∪ ⋃ W ∪ ⋃ H` satisfies:
`X` is decomposable and `X ∪ P` is decomposable.

Mode `X`: hinges take the **negative** wedges, positive occurrences use `R o`, negative ones
use `Y o`. Mode `X ∪ P`: hinges take the **positive** wedges, each edge of `P` closes its
positive slot wedge to a triangle, negative occurrences use `R o`, positive ones use `Y o`.
No physical edge is ever used twice: a physical edge with multiplicity in the integer
certificate is represented by distinct slot wedges with distinct apices, and the slot hinges
cancel a positive against a negative use.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

                                                                                     
                                      
                                                                               
      

variable {O S : Type*} [Fintype O] [Fintype S] [DecidableEq O] [DecidableEq S]

                                                                        
                                                                                          
                      
                                                  

                       
                             
                                                                            
                                                                             
                                                    
                                                                          
                                                    
                                   
                                              
                                                                 
                                                                         
                                           
                                                                   
                                                                                    
                                                        
                                                  
                                                  
                                   
                                                                      
                                                                            
                                                                         
           
                       
                                                                          
                                                              
                                                                                        
                        
              
                                                                                 
                                                       
                                                                         
                                                                                  
                                               
             
                          
                           
                                                            
                                                          
                  
                               
                          
                                             
                                                                   
                 
                                                                   
                                                                       
                     
                                                
                                                  
                            
                                                
                                                      
                                                  
                                          
                                                
                                               
                              
                                                          
                                                         
                                     
                                                                   
                                      
                                          
                                
                                                                                     
                   
                         
                                    
                                                                
         
                                                                                          
                                  
               
                                                  
                                             
                                             
                                    
                        
                                               
                           
                                    
                                             
                                                    
                                                                                  
                                                   
                                                                      
                 
                       
                                                                       
                                    
                                                                                            
         
                                                                                           
                                                         
         
                          
                                                                                
                                                          
                                                                                        
                       
               
                                                      
                                                                 
                              
                                                                                      
                                                                               
                                                                 
                              
                                       
                                                                                         
                             
                                                                               
                      
               
                  
                                                 
                      
                         
                            
             
                      
                                                                                            
                
                   
                                                                       
                                     
                                     
                                                                             
                                                   
                    
                    
                                  
                                    
                                                                 
                            
             
                      
                                                                     
                   
                                                                      
                              
                                     
                                                                      
                                                   
                    
                    
                                           
                             
           
                    
                                                                              
                 
                                                                      
                  
                                   
                                                
                                                                  
                                   
                  
                      
                                                    
                                                                   
                                                         
           
                    
                                                                                            
                                                                   
                
                                 
                                              
                                               
                
                
                   
                  
                                               
                      
                         
                            
             
                      
                                                                    
                   
                                                                      
                              
                                     
                                        
                                                                             
                                                                       
                    
                    
                                           
                            
             
                      
                                                                                           
                
                   
                                                                       
                                     
                                     
                                        
                                                                             
                                                                              
                    
                    
                                  
                                    
                                                                  
                             
           
                    
                                                                             
                 
                                                                      
                  
                                   
                                      
                                             
                                     
                           
                      
                                                                                  
                                                 
                                          
                                                 
                                   
                  
                      
                                                    
                                                                
                                                  
              
                              
           
                    
                                                                                             
                 
                                                                       
                  
                                   
                                      
                                              
                           
                      
                                                                                  
                                                 
                                          
                                     
                                                 
                  
                                   
                      
                                                    
                                                                
                                                  
              

end PartitionedTriangleAbsorption.SignedHinge
