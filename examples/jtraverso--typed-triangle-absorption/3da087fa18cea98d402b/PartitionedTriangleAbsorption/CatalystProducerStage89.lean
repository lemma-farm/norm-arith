/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystSeparationStage89

/-! # End-to-end producer: deployment, catalyst reservation, insertion

From an even physical configuration `X` we run, in order:

1. the Stage87 deployment to a `0`/`2`-configuration `Y`, with its terminal
   ledger `L` (Stage88-style, keeping the continuation);
2. the catalyst selection outside `B ∪ L`, the active vertices and `Z`;
3. the retrospective framing of the catalysts `D` through the deployment;
4. the token-tracked insertion of all catalysts by Stage87 exchanges, with
   history starting at `L ∪ D` and forbidden vertex set
   `Z ∪ A ∪ (catalyst vertices)`.

The output is an actual physical trace from `X ∪ D` (history `U ∪ D`) to the
final token-tracked configuration, which is 2-regular, plus all the
separation data of `CatalystSeparationStage89`. Explicit budget:
`|Z| + 176 |X| + 4(d + |U|) < a`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89 PhysicalMovesStage86
  CatalystFramingStage89

variable {V : Type*} [DecidableEq V] {t : ℕ} [Fintype V]

                                                                                 
                                                                       
                                                                           
                                                                      
                                                
                                                                
                                                                
                                           
                                            
                                              
                                               
                                           

                                                                                     
                                                                          
                                                                                     
                            
                                          
                                                           
                                                             
                                                 
                                                           
                                                                   
                                                   
                                                            
                                    
                                        
                                                       
               
               
                
                   
                 
                         
                     
                                                                      
                                                                   
                   
                                                                      
                                                                               

                                                                         
                                                                          
                                                                 
                                                                            
                                                                         
                                                                              
                                                            
                                            
                                      
                                                               
                                  
                                                           
                                          
                                                               
                                                                 
                                             
                   
                                                                           
                                                               
                                              
                                                      
                           
                                                        
                                                                              
                                  
                                            
                                                                  
                                                                                 
                                                   
                                                           
                                                                
                                                  
                                                                             
                                                                    
                                     
                                             
                                                      
                                                       
                                                  
                                                                                      
                                        
                                                                            
                   
                                                          
                                                                
              
                                           
                          
                              
                                                                                             
                                                                               
                                                                            
                                                   
                                                                   
                                                       
                                                                                       
                       
                                                                                 
                                                      
                                                    
                       
                                                                  
                                                                           
                                             
                                                               
                       
                                           
                                         
                                
                                                       
                                                    
                                                                       
                                                                                         
                                                                                             
                                      

                                                                             
                                                                           
                                                                    
                                                                        
                                                                               
                                                                         
                                                                    
                                                                                     
                                                                                     
                                                                        
                                                        
                                                                                                  
                          
                   
                                                                                

end PartitionedTriangleAbsorption.CatalystInsertionStage89
