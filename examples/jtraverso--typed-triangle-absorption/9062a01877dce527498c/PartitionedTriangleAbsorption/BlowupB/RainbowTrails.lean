/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.OddAbsorber

/-! # BlowupB.RainbowTrails — admissible trails for the rainbow type `{0, 1, 2}`

For the single rainbow type `R3 = {{0,1,2}}` every edge joins two different classes, and can be
oriented cyclically, from class `c` to class `c + 1` (`Arc`). Integral divisibility says that
at every vertex the two other classes receive the same degree (`degVec_R3_eq`), so in-degree
equals out-degree. A fibrewise bijection gives a permutation `σ` of the arcs with
`tail (σ i) = head i` (`trailPerm`): closed trails along which the class increases by one at
each step — the non-reversing transitions — and whose trail edges are exactly `P`
(`srcE_trailPerm`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

/-- The single rainbow type. -/
def R3 : Finset (Multiset (Fin 3)) := {{0, 1, 2}}

                                                            

                                                                            
                               

                                                                                          
                             

                                   

section Count

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

                                                                                         
                                                                                  
                                 
            
                                        
                                               
                        
                             
                         
                 
                   
                       
                                                       
                                 
                                 
              
                                 
                 
                    
                   
                      
                                                       
                          
                     
                                            
              
                                 
                               
                    
                   
                      
                                                       
                     
                          
                                            
                             
                                             
                 
                   
                      
                                                       
                     
                     

                                                            
                                                                                
                    
                                                                                  
                                                                           
                                                                      
                                                                   
           
                                                         
                                             
                                                                

end Count

/-! ### Arcs and trails -/

section Trails

variable {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 3) (P : Finset (Sym2 V))

/-- Arcs of `P`, oriented from class `c` to class `c + 1`. -/
abbrev Arc : Type _ := {uw : V × V // s(uw.1, uw.2) ∈ P ∧ p uw.2 = p uw.1 + 1}

variable {p P}

/-- Tail and head of an arc. -/
def Arc.tail (i : Arc p P) : V := i.1.1
def Arc.head (i : Arc p P) : V := i.1.2

theorem Arc.cls (i : Arc p P) : p i.head = p i.tail + 1 := i.2.2

                                                                   
                                                                        
                                                                                          

                           
                                              
                                                                   
                         
                           
                                                                      
                                                  
                    
                       
                      
                                
                                         
                      
                                
                                                        
                                                    
                                                               
                             
                              
            
       
                       

                           
                                              
                                                                   
                         
                           
                                                                      
                                                                                            
                    
                       
                      
                                
                           
                      
                                
                           
                             
                              
            
       
                       

                                                                          
                                                       
                                                         
                            
                                                                           
                          
                                                            
                                                        
                                                                                                        
                             
                                                                                                
                        
                            
                                                                         
                                     

                                   
                                                                 
                                                                                             
                           
                                                      
                                                           
                             
                     
                          

                                                        
                                                                              
                                                    
                                                                  

                                                               
                                       
                            

                                                
                                                              
                                                  
                                  

                                                                       
                                          
         
                              
                  
                                

                                                               
                                                              
                          

                                                                                     

                                                                                   

                                                       
                                                                                  
               
                                   
                                                    
                                      
           
                                            
                                            
                     
                                     

                                                                         
                                               
                                           
                                            
       
                                                                 
             
                                
            
                                   
              
                           
                                 
                                     
                                                           
                                                                          

end Trails

end PartitionedTriangleAbsorption.BlowupB
