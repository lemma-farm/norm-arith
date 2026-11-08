/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0RigidBoost

/-! # The common-neighbour hypothesis `CN6` (NEW candidate geometric hypothesis)

`CommonNbrRich r p J β`: for every root set `R` with `|R| ≤ r` and each colour
`i`, at least `β n` vertices `w` of colour `i` are adjacent in `J` to every
member of `R` (the empty `R` included). `CN6 = CommonNbrRich 6`.

This hypothesis is **not** claimed to follow from Theorem 13.16, from the
application, or from Stage36; it is an explicitly labelled new assumption.

Here we prove the deletion robustness (`commonNbrRich_of_delete`) and that it
implies `AntiEdgeful` (`antiEdgeful_of_commonNbrRich`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0Geometric

open Finset TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                          
                                                                                  
                     
                                           
                                                                                         

                                              
                                                                                     
                       

                                                                                
                                                                                  
                                                                                  
                                        
                                                                                      
                                 
                                                                                  
                                
                                                                                   
                                                                             
                                                              
                                                                
                                                                   
                                           
              
                                                       
                                    
                                                          
                   
                              
                                                                                    
                                                                    
                                                            
                                                
                                                                                      
                                                                              
                       
            
                                                        
                                                           
                                                     
          

                                                                                  
                                                                               
                                                    
                                                                              
                                                                     
                                                                                  
                                                                         
                                      
              
                                                 
                      
                                       
                                                        
          

                                                                
                                                            
                                                                     
                                                                                  
                                                                               
                                                                    

                                                                                  
                                                                         
                                                                                   
                              
                             
                                                
                   
                                            
                                                                         
                                          
                                     

                                                   
                                                                       
                                                                                           
                                                                            
                                        
                   
                                                     

                                                          
                                                                           
                                                                                             
                                                                                        
                                                
                   
                                                     

end PartitionedTriangleAbsorption.F0Geometric
