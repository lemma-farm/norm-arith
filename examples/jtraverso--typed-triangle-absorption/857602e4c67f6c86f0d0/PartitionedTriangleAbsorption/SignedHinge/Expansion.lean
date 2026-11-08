/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups
public import PartitionedTriangleAbsorption.SignedCertificate.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! # Expanding a signed certificate into occurrences, slots and an edge matching

A certificate term `c_j t_j` contributes `|c_j|` **occurrences** of the actual triangle
`t_j = {r j 0, r j 1, r j 2}`, with the sign of `c_j`; each occurrence has three **slots**,
one per edge (`edgeOf`). For every physical edge `e`,

  `#positive slots on e = [e ∈ P] + #negative slots on e`,

which is exactly the certificate identity at `e`. Gluing fibrewise bijections gives a
bijection `μ : positive slots ≃ P ⊕ negative slots` preserving the physical edge
(`exists_slot_matching`). This is where the integer multiplicities are resolved: an edge
used `m` times positively and `m - [e ∈ P]` times negatively gets `m` distinct positive
slots, each matched to its own partner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset SignedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

                                                                         
                                                   

                                                                 
def edgeOf (a b c : V) : Fin 3 → Sym2 V := ![s(a, b), s(a, c), s(b, c)]

                                   
                                                                            
                                                

                   
                                                                               
                  
                                                            
                                                                
                                                                  
                                                                                    
                                                                  
                                                               
                           
                                              
                             
                                                
                               
                                                  
                                                             

                   
                                                          
                                                                             
                                                              
                                  
                                                       
                                                                                    
                                                                                   
                  
           
                                               
                                    
                                    
                                              
                          
                                       
                                                                                
                                                         
           
                       
                                                  
                                                  
                       
                        
               
                                                                                       
                 
                    

                   
                                                                       
                                                                                      
                                                                                       
                                                              
                                    
                                              
                                                            
                                                                                         
           
                           
                                                                                   
                                                                                
                                                                        
           
                                                                 
                                                                            
                                                            
                                          
                                                                              
                                                                           
                                                                               
                                                  
                                                                                     
                 
                                                                                       
                       
                                    
                                                                      
                                     
                                         
                                                       
                                                                      
                                                                        
                        
                                                                                          
                                      
                                                                                      
             
                           
                                
                                                                        
                                                                   
                                                                                     
                                                                                             
                                            
                                                                                                  
                                        
                       
                                                                    
                                        

end PartitionedTriangleAbsorption.SignedHinge
