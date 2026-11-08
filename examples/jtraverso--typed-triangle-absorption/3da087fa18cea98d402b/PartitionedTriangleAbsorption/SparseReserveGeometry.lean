/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveCoverDown

/-! # Physical independence blocks and deterministic survival for a sparse reserve

For a fixed pair of distinct roots, different common neighbours use disjoint
two-edge blocks. Removing an edge set of maximum degree `d` loses at most `2d`
common neighbours. Neither result asserts existence of a random reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SparseReserveGeometry

open Finset AntiEdgeSelection ReserveCoverDown

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

                   
                                                                  
                                                      
                                 
                                                      
                         
                 
                                                             
                                                     
           
                                                    
                  
                                         

                                                                             
                                                                          
                                                           
                                                                
                                                                                     
                           
                    
                                  
                                                               

                                                  
                                                            
                                                                            

                                                                 
                                     
                                                              
                                  
                                                            
             
                      
           
                     

                                                                      
                                                
                                                                            
                                     
                                                       
                                                                 
                                              
           
                                    
                                                                 
                                                                 
                                                
                                                             
                                                                    
                                                  
                                                    
                                      
                                               
                                               
                                                                        
                                                 
         
                                                                  
                                                             
                                              
         
              
          

                                                                         
                                             
                                                         
                                                                            
                                      
                                 
                                                                            
                                                    
                                                  
                                        
                                                         
           

end PartitionedTriangleAbsorption.SparseReserveGeometry
