/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystProducerStage89
public import PartitionedTriangleAbsorption.EdgeTypeMatchingStage91

/-! # Integrating the completed catalyst return with type-preserving deployment

The return's producer is strengthened only at its deployment call: Stage90
retains the selected labels and hence the edge-type vector. All catalyst
selection, framing, insertion and separation proofs are reused unchanged.
No terminal triangle decomposition or private absorber is claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

open Finset AntiEdgeSelection TypedTransformer PhysicalMovesStage86
  CatalystSelectionStage89 CatalystFramingStage89 CatalystInsertionStage89

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

                                                                           
                                                                     
                                     
                                                            
                                            
                                      
                                                               
                                  
                                                           
                                          
                                                              
                                                                      
                                                          
                                                                                     
                                                        
                                                    
                                                              
                                
                                                    
                                                   
                                                       
                                                        
                                                                         
                                                                                 
                                                                                 
                                                  
                                                                           
                                                             
                                                                     
                                                
            
                                                      
                                                                                   
                
                                                          
                                      
                                                                   
                                                         
                                                                       
                                    
                                                 
                                                                        
                                    
                                                      
                                          
                                                                  
                       
                                                            
                                                                       
                                                        
                                                                               
                              
                                                         
                                      
                                                                               
                                                                                           
                                              
                                         

                                                                              
                                                                         
                                                                              
                                                            
                                            
                                      
                                                               
                                  
                                                           
                                          
                                                               
                                                                 
                                             
                   
                                                                           
                                                                                             
                                              
                                                      
                           
                                                        
                                                                              
                                  
                                            
                                                                  
                                                                                 
                                                   
                                                           
                                                                
                                                  
                                                                             
                                                                    
                                     
                                             
                                                      
                                                       
                                                  
                                                                                             
                                        
                                                                            
                   
                                                          
                                                                
              
                                           
                          
                              
                                                                                             
                                                                               
                                                                            
                                                   
                                                                   
                                                       
                                                                                       
                       
                                                                                 
                                                      
                                                    
                       
                                                                  
                                                                           
                                             
                                                               
                       
                                           
                                         
                                
                                                       
                                                    
                                                                       
                                                                                                
                                                                                             
                                      


                                                                          
                                                                              
                                                                    
                                                                       
                                        
                                                          
                                                         
                                                                       
                   
                         
                                
               
                                        
                                        
               
                                 
            
                                                                                       
                   

end PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

