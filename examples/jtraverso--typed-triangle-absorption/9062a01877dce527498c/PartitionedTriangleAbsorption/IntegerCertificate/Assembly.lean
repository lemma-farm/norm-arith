/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Hubs
public import PartitionedTriangleAbsorption.IntegerCertificate.Divisibility

/-! # Assembling edge and vertex reductions

`hubReduces_ind`: if every edge `e = uv` of a loopless, even-degree source `P` satisfies
`[e] + D u + D v ≡ 0` (hub-reduction with cost `(wE, ME)`), and twice every vertex term
`2·D y` hub-reduces with cost `(wV, MV)`, then `ind P` hub-reduces with cost
`(|P|(wE + wV), |P|(ME + MV))`. The vertex terms cancel exactly because
`∑_{e ∈ P} ∑_{y ∈ e} D y = ∑_y deg_P(y) · D y` and each degree is even.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 2} {G : SimpleGraph V}

                   
                                                 
                                   
           
                               

                                                                  
                                                                            
                        
               
                                    
                                                  

                                                                                       
                            

                                                                                             
                                 
            
                                                   

                                                                   
                                                                  
                                   
                                                               
                                                         
                                                          
                                                  
                                                           
                                                              

                                                                                            
                            
                                                                                    
                                                                                 
                                                                                      
                                                                
                                                                            
                        
                                            
                        
                                  
                                                 
                                                                           
                                      
                                                          
                                                                 
                                  
                                                             
                                          
                                                              
                                                                                     
                                      
                            
                                                                                         
                       
                            
                                                       
                                                                    
                                                
                                                                       
                                                                       

                                                                                             
                                                          
                                                                                     
                                                                            
                     
                                                                                      
                                                                
                                                                           
                           
                                                                 
                                 

end PartitionedTriangleAbsorption.IntegerCertificate
