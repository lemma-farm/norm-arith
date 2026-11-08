/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystSelectionStage89

/-! # Reserving catalysts after deployment and framing them retrospectively

The deployment trace is run first. From its terminal ledger `L` we select the
catalysts outside `B ∪ L`, then carry them unchanged through the whole
deployment. Unlike `MoveLedgerStage88.ledger_with_catalysts`, the theorem
`padded_ledger` below also keeps the continuation property: any later trace
starting from the padded ledger `L ∪ D` and the padded terminal configuration
`Y ∪ D` can be prepended by the padded deployment. This is what lets the
catalyst insertion be appended to the deployment.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystFramingStage89

open Finset AntiEdgeSelection TypedTransformer PhysicalMovesStage86 CatalystSelectionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

                                                                              
                                                                        
                                                           
                                                           
                                                      
                                                                    
                                                  
                                                   
                                                             
                  
               
                                              
                    
                  
                                                        
                                              
                
                                              
                                 
                                     
                       
                                               
                                    
                                                              
                               
                
                                         
                                                                      
                                             
                                 
                                        
                                  
           
                        
                                      
                                                                                 
                                                           
             
                                        
                   
                                                
                                        
                                         
                           
                                                                            
                                                        
             
                             
             
                                                        
                          
                     
                                   
                                   
                                                                  
                                                                  
                                                 
                                                                              
                                                          
                                          
                                                                             

                                                                        
                                                                                
                                                        
                               
                   
                                           
                                                                                     
                               
                             
                            
                                                                                 
                                                             
                                                         
                                                                
                                     
                                                           
                   
         
                                                 
                  
                   
                       

                                                                          
                                                                 
                                                            
                                       
                                                           
                                                        
                  
                        
                               
            
                 
                                          
                                       
                                                                 

variable [Fintype V]

                                                                              
                                                                               
                                                                            
                                                                             
                                                             
                                                                     
                                                     
                                                                     
                                     
                                                            
                                            
                                      
                                                               
                                  
                                                           
                                          
                                                              
                                                                      
                                                          
                                                         
                                                        
                                                    
                                                              
                                
                                                    
                                                   
                                                       
                                                        
                                                                         
                                                                                 
                                                                                 
                                                  
                                                                           
                                                             
                                                                     
                                                
            
                                               
                                                                                       
                
                                                          
                                      
                                                                   
                                                         
                                                                       
                                    
                                                 
                                                                        
                                    
                                                      
                                          
                                                                  
                       
                                                            
                                                                       
                                                        
                                                                               
                              
                                                         
                                      
                                                                        
                                                                                           
                                              
                                         

end PartitionedTriangleAbsorption.CatalystFramingStage89
