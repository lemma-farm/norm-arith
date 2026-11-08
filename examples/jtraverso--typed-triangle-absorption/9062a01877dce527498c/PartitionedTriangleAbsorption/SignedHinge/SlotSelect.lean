/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Select
public import PartitionedTriangleAbsorption.SignedHinge.Wedge
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # Greedy selection of all occurrence hinges and all slot hinges

Both selections only use `HingeSupply` through `exists_hinge_avoiding` (the vertex-only
exclusion count) and the anti-edge degree for the occurrence apices. Every chosen hinge has
its non-root support disjoint from a prescribed vertex set `U₀` and from the non-root
supports of all other chosen hinges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

                                                                                             
                                                     
                                                                  
                                                                                    
                                                               
                                                                                           
                                                                                       
                                                                    
                                                                     
                              
                                                                                     
                                   
                                                              
                                                                       
                                                          
           
                                                          
                                                  
                                                                                   
                                    
       
                      
                                                
                                                                                    
                                   
              
                                       
                                                                         
                                                                            
                        
                    
                                          
               
                                                               
                       
                                                                         
                                                        
                                                       

                                                                                           
                                                                                           
                                                                                            
                                                                      
                                                                                            
                                                                      
                                            
                                                    
                                      
                                                                                
                                                                             
                                                                                
                                                                           
                                            
                                                                       
                                                                                
                                                                           
                                                        
                                                                 
                                                   
           
                                                          
                                                                        
                                                                         
                                                                               
                                                                               
       
                        
                                       
                 
                                                              
                                                                                          
           
                                                     
                                                                    
                                                                         
                              
                                                    
                                                                                           
                                                              
                                                               
                                                              
                                                                               
                                                 
                                                
                                                              
                                    
                      
                                                                      
                                  
                                   
              
                                                                       
                                                                                        
                                                                    
                                                                                         
                         
                                        
                                                   
                                                                 
                                                              
                                              
                        
                    
                                          
                                                                         
                           
                           
                           
                      
                       
                                                          
                                                       
                                                                   
                                        

end PartitionedTriangleAbsorption.SignedHinge
