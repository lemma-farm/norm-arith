/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoherentTransformer.Target

/-! # The star (signed-link) obstruction to coherent transformers

Let `v` be a vertex and `sg : V → ℤ` a signing of its neighbours such that
`sg a + sg b = 0` whenever `v a b` is an `F`-typed triangle of `G`
(`LinkSigned`): for `sg = ±1` this says the F-link of `v` is bipartite.
Then the star charge `χ_v(va) = sg a` annihilates every `F`-typed triangle
of `G`. If `v` is a root of `Hx` but not a vertex of `Hy`, and the signed
`Hx`-degree of `v` is nonzero, NO physical transformer exists.

Equivalently, a necessary (obstruction-killing) condition for every
transformer is: for every root `v` of exactly one of the two trails and every
link signing `sg` at `v`, the signed trail-degree of `v` vanishes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

                                                
                                                     
                                                                                  
                            

                   
                                                        
                                                                                            
     

                                                                  
                                                                                  
                                  
                                            
                                                              

                                   
                                                   
                                                                
                                     
                                

                                   
                                                
                                                                
                                                           
                                                                     

                                                                             
                                                                                 
                                                                 
                                                                                      
                          
                                                                
                                           
                            
                                                          
                            
                                                          
                            
                                                          
                                                          
                                                                        
                 
                                                                                      
                                             
                                                                  
                                     
                                                         
                                
                                                                                    
                    
                     
            
                                                              
                                
         
                     
            
                                                               
                                                                              
         
                     
            
                                            
                                                                                        
         
                   

variable {I : Type*} [Fintype I]

                   
                                                                  
                                                                                    
                                                                             
                                   
                                                             
                       
                            

                                                                        
                                                                             
                                                         
                                                                                       
                                                                                          
                                                                             
                                                                             
                                                                     
                           
                                                                       
                                             
                                                   
                                                            
                                                
             

end PartitionedTriangleAbsorption.CoherentTransformer
