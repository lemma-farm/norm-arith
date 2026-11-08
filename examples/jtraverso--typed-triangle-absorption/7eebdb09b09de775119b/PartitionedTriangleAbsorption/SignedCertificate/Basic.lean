/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Signed physical F0 triangle certificates

A *signed physical certificate* for an edge set `P` is a finite family of actual F0
triangles `t j` of the host `G` (three distinct vertices, all three edges in `G`, type
`001` or `011`) and integer coefficients `c j`, such that for **every** `e : Sym2 V`

  `[e ∈ P] = ∑ j, c j * [e ∈ triEdges (t j)]`.

Negative coefficients are allowed. This module proves the prerequisites requested in
Stage 49 by exchanging finite sums:

* `sum_eq_of_cert`: `∑_{e ∈ P} f e = ∑ j, c j * ∑_{e ∈ t j} f e` for every `f`;
* `charge_zero_of_cert`: every triangle-annihilating integer charge vanishes on `P`;
* `card_eq_of_cert`: `|P| = 3 ∑ j c j`, so `3 ∣ |P|`;
* `pairCount00_of_cert`, `pairCount11_of_cert`, `pairCount01_of_cert`: the signed total of
  type-`001` triangles equals the (nonnegative, physical) number of `00` edges of `P`,
  similarly `011`/`11`, and the number of `01` edges is `2 ∑ j c j`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

variable {V : Type*} [Finite V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- Integer indicator of an edge set. -/
def ind (S : Finset (Sym2 V)) (e : Sym2 V) : ℤ := if e ∈ S then 1 else 0

                                                                                       
                                                                                      
                                                                          
                                            
                                                                                        

                                             
                                            

                                                                
def pairCount (p : V → Fin 2) (E : Finset (Sym2 V)) (a b : Fin 2) : ℕ :=
  (E.filter fun e => e.map p = s(a, b)).card

                                                               
                                                                                           
                                                   

                  
                                                                                  
                                           
                                             
                                            

                                                                     
                                                           
                                                                           
                                                                                       
                                                             
           
                           
                         
                                                                                
                                                 
                                 
                                                      
                                                                         
                                                  
                                                 
                                                              

                                                                                   
                                                                                     
                                               
                                                                                
                                                                                     
                                                                      
                          
           

                                                                                      
                                                                             
                                                                                
                                                                                 
                                                 

                                  
                                                                               
                                                     

                                                                       
                                                                            
                                                                                  
                                                   
                                                                       
                                                                                  
                                                   
                                                                       
                                                                                  
                                                           
        

                  
                                                          
                                                                                             
                                                                                     
                                                                                     
                                                                          
                                                                    
                                                  
                                                                                         
               
                                      
             
       
                                                                                        
                                     
                                      
                                                               
                                                                
                    
                                            
                         
                                  

                                                                                   
                                                                                 
                                                                 
                                     
                                         
                                                      
                           
                                           
                                                                          
                          

                                                                                
                                                                                  
                               
                                                       

                                                                                   
                                                                               
                                                                                     
                                   
                                                                                         
           
                                      
             
       
                              
               

                                                                                    
                                                              
                                                                                     
                                                                 
                                                              
                                          
                                           
                                                                

                                                                                    
                                        
                                                                                     
                                                                 
                                                              
                                          
                                           
                                                                  

                                                                       
                                                                                     
                                                                 
                                                
                                              
                                           
                                                                          

                                                                               
                                                                                       
                                                                 
                                                                                   
                                                                                      
                                                                                     
                             
                                         
                      
                                                               
                                             

end PartitionedTriangleAbsorption.SignedCertificate
